# Braun shape — independent connected-case preflight

Date: 2026-11-03 UTC. Ticket: `FDSA-XT09`.

**Report-only preparation.** This report selects no implementation scope, base,
worktree, source API, validation result or acceptance. C1 attempt 3 remains the
sole authorized gate; its outputs were not inspected. The exact initial C2
prefix remains `c80eec92f5458eccfd1c34c8314d666c2a1e3847`, after repaired
Chapter 1 acceptance. The retained XT01/XT02 developments remain unaccepted.
Only this assigned report is written; all earlier obligations remain intact.

## 1. Finding and scope recommendation

There is a genuine small shared structural use: Chapter 11 arrays and Chapter
16 priority queues use the same recursive Braun condition on the same ordinary
node-labelled tree. The missing bridge is from its left-biased child counts to
almost completeness, followed by the existing height results. Arbitrary label
transport and uniqueness of the Unit-erased shape are useful laws of that same
condition. The cases below distinguish these claims without a new carrier,
executable checker, tree generator, cost model or general balancing framework.

The minimum candidate is the exact recursive predicate, its node/count forms,
arbitrary-map equivalence, equal-count erased-shape uniqueness, and a local
almost-complete constructor theorem feeding Braun-to-almost-complete. The
existing rounded-height and height-optimum results should be consumed directly.
A public recursive symmetric-balance predicate is a separate scope choice:
using its local constructor arithmetic does not by itself discharge C11-018.
The independent Exercise 11.1 proof route likewise remains explicit.

The recommended evidence is a small connected set: the existing empty,
right-two-node, repeated-three-node and sample/cache fixtures, plus two
five-node shapes that separate the remaining balance and layout claims.
Generic transport/uniqueness clients supply the universe and payload tests.
Index and operation calculations below delimit later consumers; they do not
select an array/index/heap implementation or an extra case campaign.

## 2. Definitions and actual reusable interfaces

Throughout this report, `E` means `BinaryTree.nil`, `N a l r` means the existing
**label-first** `BinaryTree.node a l r`, and `leaf a := N a E E` is just display
notation. The source prints nodes in left-label-right order. Let `n`, `ell`,
`h`, and `m` denote `numNodes`, `numLeaves`, `height`, and `Trees.minHeight`.
They have the exact recurrences:

```text
n(E)=0;       n(N a l r)=n(l)+n(r)+1.
ell(E)=1;     ell(N a l r)=ell(l)+ell(r);    ell(t)=n(t)+1.
h(E)=0;       h(N a l r)=max(h(l),h(r))+1.
m(E)=0;       m(N a l r)=min(m(l),m(r))+1.
```

For reasoning only, write `B` for the source Braun predicate and `W` for its
recursive symmetric-size variant. These are not declarations newly available
in conaled:

```text
B(E)=True.
B(N a l r) iff B(l) and B(r) and (n(l)=n(r) or n(l)=n(r)+1).
W(E)=True.
W(N a l r) iff W(l) and W(r) and n(l)<=n(r)+1 and n(r)<=n(l)+1.
AC(t) iff h(t)<=m(t)+1.
```

The Braun count condition is equivalently `n(r)<=n(l)<=n(r)+1`. Symmetric
balance uses both inequalities, or the source's integer absolute difference;
a single truncated Nat subtraction is not its definition. Both `B` and `W`
require the condition recursively. `AC` imposes neither left bias nor packing.
Source anchors are `Braun_Tree.thy:12–18`, `Tree.thy:50–65`, and
`Tree_Real.thy:61–112`; retained obligations are C11-008 and C11-014–019.

These actual interfaces were read, rather than inferred from proposed names:

| Existing public API | Connection needed by a selected future case |
|---|---|
| `BinaryTree.numLeaves_eq_numNodes_succ t`; `numLeaves_pos t` | Keep the node/external-leaf distinction and the positive logarithm argument, including nil. |
| `Trees.numNodes_map f t`, `numLeaves_map f t`, `height_map f t`, `minHeight_map f t` | A label map preserves counts and both heights, even when noninjective and across unrelated universes. |
| `Trees.inorder_node a l r`, `inorder_length t`, `inorder_map f t` | Observe ordered payload occurrences; these laws do not identify Braun array order or reconstruct shape. |
| `Trees.complete_iff_minHeight_eq_height t`; `complete_almostComplete t ht` | Reuse the exact complete/perfect-tree convention in the singleton and balanced-three fixtures. |
| `Trees.almostComplete_map f t`, `almostComplete_children a l r ht` | Existing shape transport and parent-to-child direction; the new size-sensitive constructor is the missing opposite-direction support. |
| `Trees.height_eq_clog_numLeaves t ht`; `minHeight_eq_log_numLeaves t ht` | Apply after an actual Braun-to-AC proof. `ht` is genuinely required by these statements. |
| `Trees.height_optimal s t hs hsize` | From `AC s` and `n(s)<=n(t)`, derive `h(s)<=h(t)` for independently typed trees. The competitor need not be Braun or AC. |
| `Trees.height_eq_ceil_logb_numLeaves t ht`; `minHeight_eq_floor_logb_numLeaves t ht` | The existing real-rounding bridge supplies the source meaning without putting Real analysis into the predicate. |
| `Trees.numLeaves_le_pow_height t`; `clog_numLeaves_le_height t` | Universal capacity facts usable in Exercise 11.1's independent route; their proofs do not require AC. |
| `Trees.Cached.erase`, `erase_annotate`, `annotate_valid`, `read_annotate`, `read_eq_fold`, `numNodes_erase` | Compose shape transport with actual annotated values, keeping recursive cache validity separate from Braun shape. |

No public Braun name is frozen by this report. Calls to a future predicate law
must be connected to its actual final interface before implementation; a proof
of a concrete numeral alone would not exercise that new public law.

## 3. Independent shape calculations and strict boundaries

### Existing fixtures and smallest domains

The exact XT01 fixtures are `TreeCacheExamples.balancedThree`, `leftThree`,
`sample`, `sizeSample`, `corrupt` and `chain`. XT02 already has
`TreeShapeExamples.single`, `rightTwo`, `perfectThree`, and their shape facts.
In particular, `chain 2` is the left-only two-node shape. No replacement
fixtures are needed for these observations.

| Actual fixture or displayed shape | Child counts at root | `n` | `ell` | `h` | `m` | `B` | `W` | `AC` |
|---|---:|---:|---:|---:|---:|---|---|---|
| `E` | — | 0 | 1 | 0 | 0 | true | true | true |
| `single` / `leaf a` | 0 / 0 | 1 | 2 | 1 | 1 | true | true | true |
| `chain 2` / `N a (leaf b) E` | 1 / 0 | 2 | 3 | 2 | 1 | true | true | true |
| `rightTwo` / `N a E (leaf b)` | 0 / 1 | 2 | 3 | 2 | 1 | false | true | true |
| `balancedThree` / `perfectThree` | 1 / 1 | 3 | 4 | 2 | 2 | true | true | true |
| `leftThree` | 2 / 0 | 3 | 4 | 3 | 1 | false | false | false |
| `sample` | 1 / 2 | 4 | 5 | 3 | 2 | false | true | true |
| `B5` defined below | 2 / 2 | 5 | 6 | 3 | 2 | true | true | true |
| `A5` defined below | 3 / 1 | 5 | 6 | 3 | 2 | false | false | true |

Each row follows by the displayed recurrences, not by executing a proposed
Braun implementation. For example, `sample` has a left leaf and a right
left-only two-node child. Those child heights are 1/2 and minimum heights
1/1, hence root heights 3/2; its right-larger root violates Braun despite the
recursive symmetric condition. Its existing inorder is `[0,1,2,3]`, so
ordered payloads do not determine Braun shape either.

The two orientations of the two-node shape prove that `B -> W -> AC` has
strict implications once paired with `A5`. Their Unit-erased trees differ
despite equal size and symmetric balance. They also expose the empty-child
boundary: in a Braun node, empty left forces empty right; empty right permits
a singleton left. The two child-emptiness conditions are not equivalent.

`balancedThree` and `leftThree` both have inorder `[1,1,1]`. The existing
`same_inorder_different_height` states their equal inorder and heights 2/3.
The former is Braun and complete; the latter is neither Braun nor AC.
Therefore neither node count nor even the full ordered list of repeated
payloads determines shape, balance or height. The direct power expression is
`2^2=4<=7` for the balanced tree, but `2^3=8>7` for the chain.

The recursive qualification is also necessary. Put two copies of the existing
`leftThree` below one root. The root has equal counts 3/3, but the resulting
heights are `h=4`, `m=2`, so AC fails (`4>2+1`). Root count equality cannot
replace the constructor's two AC child hypotheses, or the recursive child
premises of Braun. This is a substitution into the same retained fixture,
not another balancing abstraction.

### The five-node pair

Use arbitrary labels, with no assumed equality, order, or distinctness:

```text
B5 = N a (N b (leaf d) E)       (N c (leaf e) E).
A5 = N a (N b (leaf d) (leaf e)) (leaf c).
```

For `B5`, both children have `(n,h,m)=(2,2,1)`, and each is left-biased.
The parent has `(n,ell,h,m)=(5,6,3,2)` and satisfies Braun. For `A5`, the
children have `(3,2,2)` and `(1,1,1)`. The parent has the same four structural
measurements and is AC, but its count gap is 2, so both `W` and `B` fail.
Their erased shapes differ: `B5` has two nodes in each child, while `A5` has
three and one. This refutes erased-shape uniqueness when either Braun premise
is replaced merely by AC; the two-node pair already refutes replacement by
recursive symmetric balance.

The source one-larger constructor and the equal-size constructor address
actual different cases. A leaf on the left and nil on the right gives the
smallest one-larger instance, with `k=ell(right)=1` and parent heights 2/1.
The equal-size `B5` root has `k=3` on both sides and parent heights 3/2.
No positive-node assumption on the right child is legitimate.

For the general one-larger constructor, `k=ell(right)>=1` and `ell(left)=k+1`.
The expected public observations are exactly
`h(parent)=Nat.clog 2 (k+1)+1` and `m(parent)=Nat.log 2 k+1`. From
`2^i<=k<2^(i+1)` one gets `2^i<k+1<=2^(i+1)`, not the same weak/strict ends.
These are the C11-015 intermediate identities, not merely a conclusion that
some proof of AC succeeds. Real floor/ceiling expressions must use the existing
rounding bridge if those identities are selected for implementation.

A future Braun-to-AC application on `B5`, followed by the actual
`height_eq_clog_numLeaves` and `minHeight_eq_log_numLeaves`, should produce
`Nat.clog 2 6=3` and `Nat.log 2 6=2`. The same existing AC theorems also apply
to `A5`. `height_optimal` makes either tree's height minimal among trees with
at least five nodes, even across payload universes. Thus minimum possible
height and both exact rounded-height equalities do not characterize Braun.
The existing `counter_height_optimal` / `counter_not_almostComplete` already
supply the stronger warning that optimal maximum height alone need not even
imply AC; no new fixture is required for that additional boundary.

## 4. Generic labels, erasure, empty types and caches

### Transport and the exact uniqueness conclusion

A useful general connected client has `s : BinaryTree α`, `t : BinaryTree β`,
with `α : Type u` and `β : Type v` independently, hypotheses `B s`, `B t`,
and `n(s)=n(t)`. Its conclusion is

```text
s.map (fun _ : α => ()) = t.map (fun _ : β => ()).
```

It is an equality in the existing `BinaryTree Unit`. There is no need for a
new quotient, `HEq`, common payload type, label equality decision, total order,
or finite/inhabited instance. At a nonempty root of total size `N`, Braun
forces child counts `N/2` and `(N-1)/2`; alternatively the two inequality pairs
and equal parent totals force equality of corresponding child counts directly.
Recursive uniqueness applies to those children. This is an at-most-one-shape
claim, not an existence theorem or a canonical labelled constructor.

The companion map client should consume an equivalence
`B(t.map f) <-> B t`, not only a forward implication. Existing
`numNodes_map`, `height_map`, `minHeight_map`, and `inorder_map` then connect
unchanged shape measurements and mapped semantic occurrences. A constant map
to Unit is intentionally noninjective and cannot repair the shape of `sample`
or `leftThree`. A relabelling preserves child positions, not arbitrary tree
rotations or permutations.

Two singletons carrying `false` and `true` have equal Unit-erased shapes and
all equal measurements, yet are different Bool-labelled trees with inorder
`[false]` and `[true]`. This is the smallest failure of raw payload equality.
It also prevents treating uniqueness by size as canonical array-content
representation; C11-133 needs the actual array-order observation and its
injectivity on valid trees, in addition to shape.

For `t : BinaryTree Empty`, the actual `TreeCacheExamples.empty_tree t`
gives `t=E`; XT02 `empty_shapes` and `empty_logarithms` already connect the
existing shape/log laws. A future Braun specialization should join those
clients: `n=0`, `ell=1`, `h=m=0`, and both rounded logs of 1 are zero.
`BinaryTree Empty` itself is inhabited by nil, while `Empty` is not. No payload
default may be inferred. The statement that a Braun tree exists at every
natural size over every payload type is false at size 1 over `Empty`.
The same no-node reasoning applies to an entry type such as `Nat × Empty`.
Generic structural laws are meaningful without manufacturing an entry.

### Actual cache compositions and counterexamples

XT01's `Cached.erase` is exactly `map Prod.fst`; it retains semantic labels
and removes annotations. A Braun map equivalence should therefore give
`B(Cached.erase t) <-> B t` for arbitrary annotated trees, with no
`Cached.Valid` premise. Composing that law with the actual `erase_annotate`
gives `B(annotate empty combine t) <-> B t` for every supplied fold algebra.
It does not require a monoid, a cache-correctness assumption or an extra tree
carrier. This is a genuine structural use of the existing annotation API.

For the actual size algebra, `Cached.read_annotate 0 sizeStep t` together with
`Trees.fold_numNodes t` gives the new annotation's root read `n(t)`;
`Cached.annotate_valid 0 sizeStep t` separately establishes recursive validity.
For an arbitrary existing annotated tree the reader-to-fold theorem instead
requires its actual `Cached.Valid` proof. Neither reader fact requires Braun.
The new shape transport and existing cache theorem have different premises
and should remain distinguishable in a combined client.

Two existing values expose both omitted-premise mistakes:

- `TreeCacheExamples.sizeSample` is recursively valid by `sizeSample_valid`
  and erases to `sample` by `sizeSample_erases`. Its root child counts are
  1/2, so its shape is not Braun. Correct size annotations do not establish
  left-biased balance.
- `TreeCacheExamples.corrupt.left` is exactly `N (0,2) E E`. Its shape is a
  Braun singleton, but `Cached.Valid 0 sizeStep` would require
  `2 = sizeStep 0 0 0 = 1`, which is false. Braun does not certify a cached
  size. This is a new expected observation of an existing value, not an
  existing public theorem being claimed here.

These examples use the actual recursive XT01 validity predicate. The source
array wrapper has a different cache representation: `Array_Braun.thy:147–153`
stores one global length alongside the tree and requires
`B t and cachedLength=n(t)`. For example, a Braun singleton paired with cached
length 2 has a wrong wrapper cache. That is a separate invariant conjunct,
not a reason to redefine source arrays as XT01 per-node annotated trees.

## 5. Array order, heap order and actual residual shapes

This section records source boundaries for later clients. It proposes no new
index operation, heap implementation, cost observer or dependency on XT08.

### Low-bit indices are a different observation from inorder or BFS

The source index recurrence is
`I(E)={}` and `I(N a l r)={1} union 2*I(l) union (2*I(r)+1)`
(`Braun_Tree.thy:47–49`). It reads low path bits first. Consequently the
left-right path has index 6 and the right-left path index 5. Conventional
heap-path/BFS numbering gives those paths 5 and 6, respectively.

| Shape | Source low-bit indices | Conventional heap-path positions |
|---|---|---|
| `rightTwo` | `{1,3}` | `{1,3}` |
| `B5` | `{1,2,3,4,5}` | `{1,2,3,4,6}` |
| `A5` | `{1,2,3,4,6}` | `{1,2,3,4,5}` |

Thus Braun left bias is not conventional breadth-first left packing.
For `B5`, local child indices `{1,2}` become `{2,4}` and `{3,5}`; this
independently computes its contiguous source set. `A5`'s complete left child
has local indices `{1,2,3}`, becoming `{2,4,6}`, beside right index 3.
Its conventional breadth-first packing does not rescue Braun validity.
These finite calculations do not prove either direction of the general
index-set characterization C11-009–013.

The actual array list at `Array_Braun.thy:28–30` is root followed by a splice
of child lists. For `B5` it is `[a,b,c,d,e]`, whereas inorder is
`[d,b,a,e,c]`. Distinct payloads make the observation difference visible.
For completeness, the source's complete seven-node shape labelled by low-bit
indices has root 1, left child 2 with children 4/6, and right child 3 with
children 5/7. Direct splice expansion gives `[1,2,3,4,5,6,7]`; BFS gives
`[1,2,3,4,6,5,7]`; inorder gives `[4,2,6,1,5,3,7]`. This is an observation
boundary, not a request for a further checked indexing-case family.

Shape uniqueness does not establish array lookup domains, contiguous indices,
array-order injectivity, or the conversion/representation laws. Those retain
their original C11-009–013, C11-094/095 and C11-133 obligations. Likewise
C11-125's prefix-consuming `Balance.bal` consumes in inorder, even when its
result is Braun; its returned shape does not change that semantic contract.

### Heap order is independent of Braun

Use the same two-node shapes with natural-number labels. The left-only tree
`N 1 (leaf 0) E` is Braun but is not a min-heap: its root 1 exceeds the stored
0. The right-only tree `N 0 E (leaf 1)` is a min-heap but not Braun. Hence
neither component of Chapter 16's validity `B and heap` follows from the
other. Singleton and repeated labels are permitted; Braun never compares them.

The actual source `get_min` returns the root. Its leastness theorem requires
heap order and nonemptiness (`Priority_Queue_Braun.thy:41–45`), so the first
case gives root 1 and actual minimum 0. A generic label map preserves Braun
but need not preserve heap order: the natural map `x -> 1-x` changes the
Braun min-heap `N 0 (leaf 1) E` into that failing example. No heap monotonicity
claim is included in the proposed arbitrary-label structural transport.

### Ordinary extraction and Braun extraction rebuild different trees

The exact source ordinary `Tree_Set.split_min` rebuilds `N a l' r` after a
recursive extraction from `l` (`Tree_Set.thy:35–37`). Braun priority-queue
`del_left` rebuilds `N a r l'` (`Priority_Queue_Braun.thy:77–79`). On the
existing `balancedThree`, the complete outputs are therefore:

```text
ordinary split_min: (1, N 1 E (leaf 1)).
Braun del_left:     (1, N 1 (leaf 1) E).
```

Both remove one occurrence and leave count 2 and inorder `[1,1]`. The ordinary
residual has the `rightTwo` shape and is not Braun; the swapped residual has
the `chain 2` shape and is Braun. Equality of remaining repeated payloads or
multisets would hide this distinction. The expected residual shapes follow
from the actual branch equations, not from an assumed content specification.

With generic labels on `N a (leaf b) (leaf c)`, the corresponding residuals
are `N a E (leaf c)` and `N a (leaf c) E`. Their inorders are `[a,c]` and
`[c,a]`; they differ when `a` and `c` differ. Consequently Braun `del_left`
does not inherit ordinary extraction's general head/inorder-tail equation.
This is one connected substitution of the same three-node shape, not an
implementation of either operation in this report.

C16-021 and C16-026 therefore need proofs for the swapping recurrence. The
useful arithmetic is exact: from `n(l)=n(r)` or `n(l)=n(r)+1`, and successful
extraction's `n(l)=n(l')+1`, derive `n(r)=n(l')+1` or `n(r)=n(l')`.
Together with the actual child Braun proofs this establishes the assembled
parent `N y r l'` needed by sift. Two separately Braun children alone are
insufficient; they must also satisfy the sibling count condition. This is a
real later use of the shared invariant, not an operation equality or a cost
bridge from XT08.

## 6. Height routes, model limits and retained obligations

Braun-to-AC followed by XT02's exact logarithm theorems supports C11-017 and
the height input for C16-042. The empty case uses `ell=1`, so no positive-node
restriction or replacement of `n+1` by `n` is legitimate. None of these
structural theorems charges comparisons, visits, reconstruction, size reads,
cache verification or machine runtime.

**C11-122 / Exercise 11.1 remains an independent proof obligation.** The book
pp.146–147 specifically asks first for the direct inductive bound
`B t -> 2^(h(t))<=2*n(t)+1`, without proving AC first, then for exact ceiling
height. `Priority_Queue_Braun.thy:22–36` supplies an actual direct proof route.
The existing universal capacity result `ell<=2^h` may be reused. For a
nonempty tree write `h=j+1`; the direct bound gives `2*2^j<=2*n+1`, hence
`2^j<=n<ell`, which identifies the ceiling along with `ell<=2^h`. Nil is the
separate `ell=1`, `h=0` case. This argument does not call Braun-to-AC.
If the minimum shared scope excludes the direct proof, the row must remain
mandatory later C11 work. Neither these calculations nor the AC proof waive it.

The same two-node orientation boundary retains Exercises 11.2/11.3:
left-spine lengths are 2 and 1 for left-only and right-only trees, while both
maximum heights are 2. Symmetric balance cannot yield Braun's left-spine
height equality, or the oriented child-height conclusion
`h(l)=h(r) or h(l)=h(r)+1`. Their actual observations and proof routes remain
C11-123/124. The selected structural layer need not introduce a spine executor
just to state this warning.

The source height-to-time use is conditional on the actual operation model.
Chapter 16 separately proves a raw insertion bound `T_insert<=h+1`, a
nonempty `T_del_left<=h`, assembled-Braun sift bounds, and `B -> T_del_min<=2*h`.
The completed source report records their generated tariffs and the distinct
zero branches. Only after those correspondences may height be substituted by
`ceil(log2(n+1))`. The empty/hit/base conventions of other shared measured
executors must not be copied into these operations. No Braun-checker runtime
or asymptotic theorem follows from the finite shape cases in this report.

The complete Chapter 11 inventory and all eight exercises, Chapter 16's
algorithm/validity/cost rows, and the exact original C2 prefix remain unchanged.
The source report records 135 C11 rows and 48 C16 rows; this case task inspected
the relevant structural, index, invariant, consumer and exercise rows, rather
than conducting another full inventory review. The recursive C11-018 theorem,
index converse, full array-order and cache contracts, operation preservation,
conversions, and explicit timing models retain their original owning scope.

## 7. Statement assessment and recommended connected evidence

| Intended claim | Needed hypotheses and meaningful connection | Failure exposed here |
|---|---|---|
| Exact recursive Braun condition | Arbitrary payload type; actual node/count equations, both recursive child premises. | `rightTwo` defeats missing orientation; a root over two `leftThree` children defeats a root-only test. |
| Local size-balance-to-AC constructor | Both children AC and both symmetric count inequalities. Consume existing exact height/min-height logarithm laws. | `A5` refutes the converse; equal-count malformed children show why child AC cannot be dropped. |
| Braun-to-AC and height applications | Actual Braun premise; apply the new bridge, then existing log/optimality APIs. | `A5` and `rightTwo` show the result does not characterize Braun; `n+1` remains at nil. |
| Arbitrary label-map equivalence | Any supplied map across independent universes; count-preserving actual `BinaryTree.map`. | Constant relabelling cannot repair `sample`; heap order and semantic payload equality do not transport arbitrarily. |
| Erased-shape uniqueness | Both inputs Braun and equal node counts; compare maps to Unit. | Different Bool singletons refute full labelled equality; right/left two-node and `B5`/`A5` refute weaker shape premises. |
| Annotation composition | Actual `Cached.erase` and `erase_annotate`; no cache validity for structural transport. Reader correctness uses its separate actual contracts. | `sizeSample` valid but non-Braun; `corrupt.left` Braun but invalid cache. |
| Nonempty source consumer domains | Preserve complete residual trees and source child-swapping equations. | Ordinary extraction of `balancedThree` yields a non-Braun residual despite the same remaining inorder/count. |
| Generic/empty applicability | No payload order/equality/inhabitance; concrete `Empty` nil case and independent universes. | A positive-size existence claim over `Empty` is false. |

The suggested future example file can combine these into a few general clients
and connected concrete substitutions. It should not add a case per helper or
reimplement the shape, log, cache or traversal libraries. Concrete reductions
must retain a visible application of the public law they are meant to exercise.
The expectations above were calculated independently from the source/metric
recurrences; no proposed implementation or compiler result determined them.

No concrete mathematical or API obstruction was found for this minimum pure
structural boundary. The full final source and API reports were read before
closing correspondence; their hypotheses, source domains and scope limits
agree with these calculations. Their proposed names remain proposals. Root
owns the decision to defer or freeze a later scope and its dependency base.

## 8. Exact inspected inputs and reading limits

All paths below are under `/workspace/scratch/845aa1048b05` unless a retained
Git path is specified. The complete ticket was read first and the assigned
report path was confirmed absent before writing. Project Git/source reads
used the pinned Nix environment. Ordinary SHA-256 identities identify content;
no compiler, checker or project hash helper was used.

### Retained Lean sources

The six XT01/XT02 files and the Mathlib carrier below were read completely.
XT01 and XT02 identities are original retained drafts, not a newly chosen base.

| Revision / file | Bytes / lines | SHA-256 |
|---|---:|---|
| XT01 `64c6b777d828ecfe83234fc2aed94600a1f24297` — `Applications/Trees/Observations.lean` | 4,119 / 107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| Same XT01 — `Applications/Trees/Cached.lean` | 5,668 / 135 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| Same XT01 — `Examples/TreeCache.lean` | 16,307 / 363 | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` |
| XT02 `974a97321a8ec174b56104c7e6efaaca881b6639` — `Applications/Trees/Shape.lean` | 11,019 / 267 | `2233e014900a48ebc239d676a1c8abdaee2046ef503e5219bff460a001b868f3` |
| Same XT02 — `Applications/Trees/ShapeLog.lean` | 2,796 / 69 | `35c0555383fc3d03bcac4f368d41b2c8f744a49e18ef72b192c3753b7ef4497b` |
| Same XT02 — `Examples/TreeShape.lean` | 12,648 / 297 | `2bcf2b65fa7a0eccc043c3bc7ba66d1bfdcd469489eab52d9085fdfb3db0b516` |
| Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` — `Mathlib/Data/Tree/Basic.lean` | 6,679 / 188 | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |

The carrier was read by exact Git show from the retained dependency source in
`conaled/.lake/packages/mathlib`; no build outputs or caches were inspected.
The first broad XT02 read was truncated by the tool output boundary; all three
files were subsequently reread in bounded complete chunks. No completeness
claim relies on the truncated output.

### Primary source and local control evidence

The Isabelle mirror pin is `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
The PQ companion is the retained AFP release of 2026-10-26, with archive
identity/provenance in the fully read source report. These formal companion
pins postdate the retained July 27, 2026 manuscript; they are not asserted to
be its generating revision. No fresh retrieval was made.

| Input and reading scope | Bytes / lines | SHA-256 |
|---|---:|---|
| `fdsa-control/tickets/FDSA-XT09.md` — complete | 2,921 / 48 | `66a33e78146023b718ee7a999b10be612f6b47efb5e9ea76f6c6f83379c620a5` |
| `fdsa-control/research/chapter11-obligations.md` — relevant structural/index/array/exercise rows | 51,829 / 386 | `ec4a0763833c45d4ff3cd0a06b90cb3fd270a245b61bab2c52608066554213fc` |
| `fdsa-control/research/chapter16-obligations.md` — relevant invariant/consumer/model rows | 19,617 / 166 | `180865d8315609bd24687b5ce0c2cbf7e75995769ac10db74e621cc693585108` |
| `book-source/Braun_Tree.thy` — complete | 6,544 / 183 | `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1` |
| `book-source/Tree_Real.thy` — complete | 4,280 / 114 | `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` |
| `book-source/Tree.thy` — 1–110, including carrier, metrics, balance, inorder and heap | 17,104 / 489 | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/Array_Braun.thy` — 1–55 and 140–168 | 26,980 / 713 | `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f` |
| `book-source/Priority_Queue_Braun.thy` — 1–135 and 198–220; further exact timing boundaries from the completed source report | 10,740 / 292 | `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e` |
| `book-source/Tree_Set.thy` — 30–40, exact ordinary extraction branch | 3,801 / 119 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` |
| `book-source/chapter11.txt` — 50–119 and 674–710, printed pp.128–130 and 146–147 | 36,093 / 717 | `02af7f0f1d70193fcbb6b7504aad9e1e6e6581b1414f363a2519ee30ef7b747f` |
| `book-source/chapter16.txt` — complete three-page chapter extraction | 5,055 / 100 | `14744b7e7ab8f2bcb7e6f34e6f7502f256fdda3665beb1fb312a031a334aafc3` |
| `fdsa-control/research/braun-shape-source-preflight.md` — complete final report | 28,163 / 401 | `5a11f1e66cf45870d7b0e0651445459457bdca5cf4c8ddd599c7c5ddb40d5931` |
| `fdsa-control/research/braun-shape-api-preflight.md` — complete final report | 31,657 / 514 | `cc445c1eef96e836dee9fb77a73932d221307f31b11fa58c5d0974efce4772e3` |

The manuscript extraction contains control-character artifacts; the exact
formulas above were checked against the retained theory text. Original
mathematical case calculations are given here; applicable Isabelle/AFP and
Mathlib notices and attribution for any later source adaptation remain as
recorded in the source/API reports.

The applicable policy/guidance was read from the existing source checkout:
AGENTS, the development/build sections of README, architecture/domain guidance,
GLOSSARY, ADR 0001/0010 and the example-driven-development skill. This bounded
planning task did not initiate an implementation or final-review loop. The
important application of that guidance here is to preserve independently
calculated expectations and require real public-law connections later, without
mistaking source reading or successful arithmetic for checked formal evidence.

This report makes no claim of Lean elaboration, compilation, proof audit,
acceptance, source integration, or exhaustive case coverage. No source,
existing report, inventory, ref, index, worktree, cache, active build output or
remote state was changed. Only the new assigned report was created; root owns
its later durability capture and any scope/author-release decision.
