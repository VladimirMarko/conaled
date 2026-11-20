# Chapter 9 factor algorithms and later exercises: unqualified preparation

This paper preserves the 19 November 2026 primary-reading and mathematical
preparation by `/root/balanced_interval_preparation`. Its factor algorithms,
construction/conversion plans and proposed cases remain **unqualified**; no
new Lean implementation or receiving acceptance follows from this curation.
Current requirements and receiving status are tracked in [CTB](../textbooks/CTB.json): CTB-78 integration acceptance precedes resumed book formalization. This paper is not a Lean dependency or a receiving validation receipt.

At accepted donor 072, Chapter 9 is57/110: rows 001–038,042–059 and 061 have their
bounded source qualifications. Measured operation rows 039–041/060 and 062–110
remain open. CTB-28 and the [canonical 110-row ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md)
own the complete scope. Existing cached-height work is documented in
[rebalancing](fdsa-height-rebalance.md), [updates](fdsa-height-updates.md),
[Set refinement](fdsa-height-set-refinement.md) and [logarithmic height](fdsa-height-bound.md).
The initial paper predated these increments; its old task boundaries are not
current instructions.

## Source and attributed reading

The FDSA27 July 2026 PDF had 1,742,029 bytes and SHA256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`;
[official source](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
The author completely extracted printed 112–116/physical 118–122 and visually
inspected each rendered page. Together with the earlier seven pages this covered
Chapter 9 printed 105–116, including equations, figures and notes. Figure 9.4 is
an algorithm listing. The full canonical ledger was read at SHA256
`6ade1fd1a470c64d613212098e311d2e0189f62bd82045dbb2f8f4387f426285`.
External Isabelle companions and dated AFP theories were not independently read
by this author; their correspondence claims below are attributed to the ledger.
Section 7.3, complete arithmetic/library closure and actual factor-resource
instrumentation were also not inspected in this continuation. No fresh primary
reading is asserted now.

| Printed / physical | Contents inspected | Later obligations |
| --- | --- | --- |
|112/118|Exercise 9.4 continuation; Exercise 9.5; factor datatype/invariant|C09-054–070|
|113/119|is_bal, polymorphic incr/decr, insertion/change detection|C09-071–074/080–083|
|114/120|Complete Figure 9.4 balancers and rot2|C09-075–079|
|115/121|Deletion, predecessor extraction, Theorems 9.6/9.7|C09-084–094|
|116/122|Exercises 9.6/9.7 and generalized-height chapter note|C09-095–110;061|

## Factor representation and detector boundaries

The factor carrier is the shared `BinaryTree (payload × tag)` with three tags
`Lh`, `Bal`, `Rh`. These describe exact actual child-height relations +1,0,-1.
They are not arbitrary natural caches. The recursive factor invariant Abal says:

- empty is valid;
- an Lh node has `h left = h right+1`;
- a Bal node has equal child heights;
- an Rh node has `h right = h left+1`;
- both children satisfy Abal.

Search ordering remains independent. A proved erasure bridge to the unannotated
AVL shape predicate can transport structural height bounds; it does not identify
the factor and height-cache annotated carriers or their runtime costs.

Printed 113 supplies only the nonempty equation of `is_bal`: inspect whether the
root tag is Bal. It supplies no empty equation. The detector equations are

`incr old new = (old is empty) or (is_bal old and not (is_bal new))`

`decr old new = (old is nonempty) and incr new old`.

Their two arguments may have different payload types. Empty tests inspect the
tree constructor; payload equality/inhabited instances are unnecessary. A total
Boolean extension of `is_bal empty` is a design choice requiring a reachable-call
independence proof. For insertion, empty old is handled directly, and a nonempty
old has nonempty insertion result. For deletion, the explicit old-nonempty guard
protects the call; empty new is handled by the first branch of `incr new old`.
These are proof obligations, not a license to assert that arbitrary raw calls
are independent of the chosen empty extension.

Theorems 9.6/9.7 prove the detectors correct **on the corresponding actual update
outputs**. Even two invariant-valid arbitrary trees do not make `incr` a general
height comparator: `incr empty empty=true`, while both heights are zero. Likewise
two Bal-rooted valid trees of different heights yield false. Keep operation
equations and invariant hypotheses in the detector theorems.

## Exact Figure 9.4 algorithms

Write `N_b(l,a,r)` for a factor-labelled node. The tag argument supplied to a
balancer is the **old parent tag**, before the child was changed. The returned
node tags below are part of the algorithm; preserving only the unlabeled shape
does not implement it.

| Function/case | Output |
|---|---|
| `balL AB c Bal C` | `N_Lh(AB,c,C)` |
| `balL AB c Rh C` | `N_Bal(AB,c,C)` |
| `balL N_Lh(A,a,B) c Lh C` | `N_Bal(A,a,N_Bal(B,c,C))` |
| `balL N_Bal(A,a,B) c Lh C` | `N_Rh(A,a,N_Lh(B,c,C))` |
| `balL N_Rh(A,a,B) c Lh C` | `rot2 A a B c C` |
| `balR A a Lh BC` | `N_Bal(A,a,BC)` |
| `balR A a Bal BC` | `N_Rh(A,a,BC)` |
| `balR A a Rh N_Lh(B,c,C)` | `rot2 A a B c C` |
| `balR A a Rh N_Bal(B,c,C)` | `N_Lh(N_Rh(A,a,B),c,C)` |
| `balR A a Rh N_Rh(B,c,C)` | `N_Bal(N_Bal(A,a,B),c,C)` |

`rot2 A a B c C` requires `B=N_bb(B1,b,B2)` and returns
`N_Bal(N_b1(A,a,B1), b, N_b2(B2,c,C))`, with exact tags:

| Middle tag bb | b1 | b2 |
|---|---|---|
| Bal | Bal | Bal |
| Lh | Bal | Rh |
| Rh | Lh | Bal |

The heavy-child Bal single rotations are mandatory, notably after deletion.
They differ from the heavy-child Lh/Rh cases in both output tags and height
behavior. No insertion-only simplification may remove them.

### Different domain from the height-cache family

An old Lh tag alone does not imply that the left child is nonempty. Nor does a
raw child tagged Rh imply its right/middle subtree is nonempty. For example,
`balL empty c Lh C` demands a missing heavy node; a malformed Rh-tagged singleton
as heavy child can demand `rot2` on an empty middle tree. The cache family's
nonnegative-height guard argument therefore does not transfer.

The canonical companion-derived inorder lemmas retain precisely these useful
hypotheses: balL needs Abal of the left child and `(oldTag=Lh -> left≠empty)`;
balR needs Abal of the right child and `(oldTag=Rh -> right≠empty)`. The opposite
child is unrestricted for that semantic helper law. These statements were read
in the ledger, not independently verified from the companion. Public operations
must establish every helper domain. An Option/nonempty interface or a deliberate
totalization may be used, but any stronger unconditional theorem needs its own
proof and explicit correspondence to reachable source equations.

## Exact insertion, extraction and deletion

Insertion into empty gives a Bal singleton. At a nonempty node:

- LT computes `left' = insert x left` once, calls
  `balL left' key oldTag right` iff `incr left left'`, and otherwise rebuilds with
  the unchanged old parent tag.
- GT is the mirror using `incr right right'` and balR.
- EQ returns the original node, including its annotation.

Theorem 9.6 requires Abal of the input and actual `new=insert x old`, and concludes
Abal new plus the **exact equation**
`h new = h old + (if incr old new then 1 else 0)`.
Unlike the cached-height family's semantic theorem, the companion's factor
inorder insertion theorem includes Abal to discharge partial helper domains.

`split_max` on a nonempty node returns `(left,key)` if right is empty. Otherwise
it recursively obtains `(right',maximum)`; it rebuilds with
`balL left key oldTag right'` iff **`incr right' right`**, otherwise with the old
tag. Its result is `(rebuiltTree,maximum)`. The direction is new,old, because this
detects a decrease of the known-nonempty old right child.

The required extraction theorem says that nonempty Abal input and actual result
`(new,key)` imply Abal new and
`h old = h new + (if incr new old then 1 else 0)`.
The canonical inorder law under the same invariant/domain assumptions is
`I new ++ [key] = I old`. Its empty-residual characterization is the Bal singleton.
Do not copy the cache family's invariant-free extraction theorem without proof.

Deletion preserves the left-maximum policy and reverses balancing direction:

- Empty returns empty.
- LT computes left' once and calls balR iff `decr left left'`; otherwise it keeps
  the old parent tag. GT mirrors this using balL and `decr right right'`.
- EQ returns right if left is empty. Otherwise it obtains `(left',key')` from
  the nonempty left subtree and calls `balR left' key' oldTag right` iff
  **`incr left' left`**; the no-change branch replaces the payload with key' and
  preserves the old tag.

Theorem 9.7 concludes Abal new and
`h old = h new + (if decr old new then 1 else 0)`
for actual deletion output. The old-nonempty guard in decr is necessary to include
empty input. The absence of a height change is not the absence of a structural
rotation. Inorder/list semantics and the seven common Set obligations remain
separate required conclusions.

Actual source functions use only root tags, shapes, comparisons and local
rewrites; structural h occurs in propositions, not executable branches. Later
resource proofs C09-092/093 must inspect and measure the actual factor recurrence,
including detectors and local rotations. A cached-family cost theorem attached
to the same output set would not establish those costs.

## Later exercises and generalized-height claim

### Exercise 9.4: fixed d≥1, cached implementation

Printed 111–112 replaces the signed local difference bound 1 by a **fixed integer
d≥1**, and asks for modified invariant, insertion and deletion with the same
correctness theorems. A natural d with a proved coercion bridge is acceptable.
The generalization applies to the height-cached family. Three Lh/Bal/Rh tags
cannot encode all differences up to a general d without changing the scheme.

The implemented generic cached single/double scheme uses trigger
`largerHeight = smallerHeight + (d+1)`. The corresponding code/research owners are linked above. Its
permitted local input range is one-sided, e.g. `hr-d <= hl <= hr+d+1` for balL.
The generic cache/domain/height effects, ordered-list semantics, predecessor
extraction, Set refinement and d=1 operation specialization have separate
source owners; the measured-cost specialization remains open. The invariant
alone, a sorted-list rebuild, or the AFP bounds theorem does not implement these
local updates. C09-057/058 retain simultaneous preservation and height change
0/+1 or0/−1 for every fixed d≥1.

Exercise 9.4 tells students they need not prove logarithmic height, but printed 116
explicitly asserts that height is still logarithmic. C09-061 was therefore a
formalization obligation, now represented by the accepted height-bound owner.
Its sufficient target is `h <= (d+1)*log2(leaves)`, from `2^ceil(h/(d+1)) <= leaves`.

The earlier **paper proof route**, subsequently addressed by the height-bound owner, is: let `m=d+1`. Height 0 has one leaf; positive
heights at most m have at least two leaves. At height n>m, the maximum child has
height n−1 and d-balance makes both children at least n−m. Strong induction and
monotonicity of the ceiling exponent give two child contributions at least
`2^ceil((n-m)/m)`; their sum gives the desired next block. Formalize the natural
ceiling as `(n+d)/(d+1)`, including zero and cast/log side conditions. Constants
depend on fixed d. The current checked theorem and its exact hypotheses are documented in
[the height-bound note](fdsa-height-bound.md). This retained explanation adds
no qualification or running-time conclusion.

The ledger separately records a dated AFP source with minimum-leaf recurrence
`M0=1`, `M(n+1)=M n + M(n-d)` using truncated subtraction, a matching witness, and
the exponential-base condition `c>1` and `c^(d+1)-c^d-1<=0`. Its source theories
have not been read by this agent; no claim is made here that their full closure
is checked. The chapter does not require every optimal-constant/asymptotic result
of that external work. Ledger-recorded prose corrections remain useful if it is
ported: truncation means max with zero, the minimum is a lower bound on leaves,
and leaves are not internal nodes.

### Exercise 9.5: actual linear construction

Printed 112 requires a linear-time `avl_of_list` for arbitrary lists, with
`I(avl_of_list xs)=xs` and valid cached AVL output. No sortedness or nodup premise
appears. C09-062–067 preserve successful suffix consumption, exact input length,
no default payload, and the actual cost of length/traversal/annotation work.
The Chapter 4 sequential prefix builder plus correctly cached almost-complete
shape is a proposed reuse route. A separate linear annotation pass can still
give linear total work; repeated insert or repeated structural-height/take/drop
traversals need different analysis and do not match that route by value alone.

The list `[1,1]` must retain both occurrences. The resulting tree may satisfy
AVL shape/cache and exact inorder while failing strict search order. Deducing
Set-search correctness requires a strictly ordered input hypothesis separately.
The referenced Section 7.3 was not newly read in this continuation.

### Exercise 9.6: reference conversion and single traversal

Printed 116 defines `debal` recursively: erase the old tag, convert both children,
and store `max(h originalLeft)(h originalRight)+1`. Those are heights of the
**original children**. It requires `Abal t -> Aht(debal t)`.

`debal2` must have the same result type, traverse only once, and **make no calls
to h** in its algorithm. A pair-returning traversal `(rebuiltTree,height)` or
local smart construction on recursively rebuilt children can meet that demand.
The required equality is `Abal t -> debal2 t=debal t`; since both proposed
conversions ignore the old tag, unconditional equality is a plausible stronger
target, not a proved fact. It must not be used before proof.

C09-099 requires the actual single-traversal/linear-cost recurrence. Under one
charge per recursive tree entry, an empty/node traversal has `2*nodes+1` entries;
separate helper calls and arithmetic have separately stated charges. Result
equality does not transfer this cost to repeated-height debal. Proof-only
erasure/shape/inorder correspondences transport height and abstract behavior
without adding execution to updates.

### Exercise 9.7: four constructors and direct local operations

Printed 116's `tree4` has exactly Leaf, Lh(left,key,right), Bal(left,key,right),
Rh(left,key,right). There is no separate tag field. It requests its invariant,
insertion, deletion, all auxiliaries, and Theorems 9.6/9.7.

C09-101–110 require a structural equivalence with both inverse laws and preserved
observations; exact invariant and detector transport; every rot2/balancer/
predecessor case; direct constructor-based insertion/deletion; ordered-list and
common Set semantics; and concrete recurrence/cost correspondence. A whole-tree
encode→old-operation→decode execution incurs conversion work and is not the
specified local update. A proof-only representation equivalence can transport
theorems after those operation correspondences have been established.

The ledger's `AVL_Bal2_Set` alternative is a Same/Diff return-tag scheme, not
this four-constructor exercise and not a d=2 generalized AVL implementation.
The book motivates space saving structurally: the factor moves into the
constructor instead of an additional label field. Exact compiled byte savings
need a concrete compiler/runtime layout; datatype equivalence alone gives no
such byte theorem.

## Separating mathematical cases for subsequent implementations

These cases were derived for this read-only handoff, without reading the parent's
foundation case file. They are proposals, not executed tests or independent
acceptance results. Use distinct ordered keys when testing semantic behavior;
shape-only cases need no ordering assumptions.

1. **Detector boundary:** `incr E E=true`, `decr E E=false`. A Bal singleton and
   a Bal-rooted three-node perfect tree are both valid but have different heights
   and `incr=false`. These refute an arbitrary-valid-pair height-comparator claim.
2. **Insertion detector direction:** inserting 1 into Bal singleton 2 gives
   Lh-root 2 and height growth. Inserting 3 into root 2 with left 1 gives Bal-root 2
   with the same height. The second pair detects a mistaken old/new argument
   reversal: `incr new old` would report a change.
3. **Deletion heavy-child tie:** start at Lh-root 4 with Bal-root 2(children 1,3)
   and singleton 5 on the right. Deleting 5 invokes the heavy-child Bal case and
   returns Rh-root 2, left singleton 1, and Lh-root 4(left 3,empty). Height stays 3.
   Reusing the heavy-child Lh output tags would make both new tags wrong.
   Mirror this to test balR independently.
4. **All three rot2 middle tags:** let outer A,C have equal height k≥1. If the
   middle grandchildren have heights `(k,k)`, output tags are Bal/Bal; if
   `(k,k−1)`, Bal/Rh; if `(k−1,k)`, Lh/Bal. Check all returned child tags and the
   Bal middle root, along with unchanged inorder. A tiny k=0 case cannot cover
   the latter two alternatives.
5. **Missing factor domains:** `balL E key Lh C` is outside the heavy-node
   domain. A raw Rh-tagged singleton as heavy child supplies a node but no
   required nonempty middle subtree. These separate heavy nonemptiness from
   recursive Abal and from the cache family's positive-natural guard argument.
6. **Extraction/deletion boundary:** extracting a Bal singleton gives `(E,key)`
   and `incr E old=true`. Deleting from empty must use decr's old-nonempty guard.
   Deleting an absent key preserves its valid tree and reports no decrease;
   deleting an equal root with a nonempty left subtree must use new,old for
   its extraction detector and the extracted predecessor as replacement key.
7. **Generalized invariant:** a correctly cached height 3 one-sided chain is
   d=2-balanced but not d=1-balanced. Test d=1 specialization, a d=2 exact+3
   trigger, equal heavy-grandchild heights, and generalized double-rotation
   cases with different grandchild heights. A d=1 proof cannot simply replace
   its numerals without proving the broadened inequalities.
8. **List conversion:** empty and `[1,1]` require exact inorder and AVL output;
   strict Set search correctness must not be inferred for the duplicate list.
   A successful prefix worker must preserve the unused suffix, not merely the
   selected element set.
9. **Conversion values versus cost:** a malformed factor-labelled singleton
   should be converted using its actual shape, not its old tag. On a long raw
   chain, repeated child-height traversals in reference debal differ from a
   single-pass debal2 recurrence, even if their returned cached trees agree.
   The single-pass requirement is not restricted to already balanced inputs.
10. **tree4 representation:** encode/decode each of the three nonempty
    constructors, not only Bal. Test the deletion tie from case 3 through direct
    constructor operations. Equality after whole-tree conversion is useful as
    a proof observation but cannot certify local execution or byte savings.

## Remaining proof boundary

Factor helper domains, detector contracts, every returned tag, actual local
operations, list/Set behavior and measured recurrences remain to be implemented
and checked. Construction must preserve arbitrary lists and exact suffixes;
conversion value equality does not establish a single traversal; tree4 value
transport does not establish local execution or compiled byte savings. Retain
the separate C05 balanced-interval and measured-sweep obligations. Current
receiving integration must be accepted before new book formalization resumes.
