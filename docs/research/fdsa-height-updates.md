# Cached height-balanced insertion and predecessor deletion

This increment implements the update algorithms of FDSA Chapter 9 on the
existing complete-annotation `HeightBalance` interface. `HeightBalance.Updates`
contains the raw programs, extraction domain, cache and shape proofs;
`HeightBalance.OrderedUpdates` supplies their ordered observations;
`AVL.Updates` is the ordinary height-only, tolerance-one specialization.
`Examples.HeightUpdates` connects the public contracts to the discriminating
cases. The public aggregate imports that client module.

The primary reference is the pinned FDSA edition, printed pages 107 and 109–112:
the insertion recurrence and Theorem 9.4, Figure 9.3's maximum-extraction and
predecessor-deletion recurrences, the simultaneous extraction/deletion height
contracts, Theorem 9.5 and Exercise 9.4. The canonical obligation owner is
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`.
Root visually checked those five pages; the generic and client authors also
read the complete retained proof/case papers and current public interfaces.
The source-reading attribution above distinguishes original primary inspection
from reuse of an attributed report. The measured-cost preparation below records
its own author and inspected pages. No fresh Isabelle-theory inspection is implied.

## The programs and their assumptions

The carrier is `BinaryTree (α × σ)`, with independent element and annotation
universes. A `HeightAnnotation α σ` supplies an empty summary, a complete local
combination and a height observation compatible with that combination. The
updates reconstruct through the existing smart constructor and direct `balL`
and `balR`. They do not replace a complete summary by its projected height.

`insert ann d x t` requires only a decidable strict comparison. A nil input
becomes a smart singleton. At `.node (a,s) l r`, the first guard `x<a` recurses
left and calls `balL`; the second guard `a<x` recurses right and calls `balR`.
If both guards are false, the exact original node is returned, including `s`.
That branch is equality under a linear order. Under an arbitrary `LT`, a
second-branch equation must retain the failed first guard: asymmetry has not
been assumed. A malformed equal-key node is therefore intentionally unchanged
on a linear order, rather than silently repaired.

`splitMaxOption ann d t` has no comparison, equality or inhabitedness premise.
Nil returns `none`. A node with an empty right child returns `some (l,a)`;
otherwise a successful recursive right extraction `(r',m)` returns
`some (balL ann d l a r',m)`. The remaining tree precedes the extracted payload
in the pair. Exact failure equivalence and constructive nonempty success make
the source's partial domain explicit without inventing a default element.

`delete ann d x t` reverses the insertion repair directions: left recursion
calls `balR`, and right recursion calls `balL`. With both comparisons false,
it extracts from the original left child. Failure means that child is nil, so
the original right child is returned. Success `(l',m)` yields
`balR ann d l' m r`. Thus the source's predecessor policy is preserved, including
the local rebuilding work. Sorted rebuilding or successor replacement would
not be the same program, even if it represented the same set.

## Separate raw, cache, balance and order contracts

The interfaces distinguish four observations with different premises:

| Observation | Premises | Conclusion |
|---|---|---|
| Extraction domain and raw inorder | Any natural `d`, raw input, successful equation where needed | Failure iff nil; nonempty success; `I t' ++ [m] = I t`. |
| Complete cache correctness | `CacheValid ann t`, any natural `d` | Insert/delete and the successful extraction remainder preserve every summary coordinate recursively. |
| Balance and actual height | `1 ≤ d` and `ValidD ann d t` | Insertion preserves validity with height change 0/+1; extraction and deletion preserve validity with height change 0/−1. |
| Strict-list semantics | Linear order and strict input inorder, any natural `d` | Exact equality to the existing list insertion/first-match deletion; output inorder remains strict. |

Here `I t = Trees.inorder (Cached.erase t)` is exposition only. The public
statements expose the actual observations rather than requiring a second
representation or a wrapper predicate from callers. None of the list-semantic
theorems assumes valid caches, balance or positive tolerance. Conversely, the
shape/cache proofs do not assume ordered keys or a lawful comparison relation.

The extraction identity holds even on unordered or malformed raw trees. Under
strict inorder, `strict_inorder_splitMaxOption` derives strictness of the
remainder and `x<m` for every retained key. It needs only the given `LT`.
`maximal_splitMaxOption` uses a preorder to conclude that `m` occurs in the old
inorder and every old key is at most `m`. Without strictness, the program
extracts the rightmost occurrence; it need not extract a greatest key.

All height conclusions refer to the actual structural `BinaryTree.height`.
Insertion exposes the conjunction

```text
ValidD ann d (insert ann d x t) ∧
  (height (insert ann d x t) = height t ∨
   height (insert ann d x t) = height t + 1).
```

Extraction and deletion expose validity together with
`oldHeight = newHeight ∨ oldHeight = newHeight + 1`. This form records both
cases without using truncated subtraction. The invariant and height claims
are established simultaneously in the induction; one is not assumed from the
other. Zero tolerance remains available for raw/cache/ordered observations,
but the balance-preservation claim requires positivity.

The fixed integer interpretation follows the existing checked
`int_tolerance_toNat` and signed absolute-height bridge. Positivity gives both
`1 ≤ D.toNat` and exact coercion back to `D`. A negative integer is not silently
truncated to an allowed balance parameter.

## Proof reuse

The generic proofs reuse the accepted local balancer contracts. A changed
child grows or shrinks by at most one, while the sibling retains its validity.
The old balance inequalities therefore supply the balancer's one-sided
permitted range. Its full cache preservation and actual triggered/nontriggered
height alternatives produce the next simultaneous induction result.

For example, when the left child grows, `L' ∈ {L,L+1}` and the old bounds
`L ≤ R+d`, `R ≤ L+d` imply `R-d ≤ L' ≤ R+d+1`. If the actual trigger
`L'=R+d+1` holds, then `L=R+d`, so the old parent height is `R+d+1` and the
balancer's alternatives are precisely the old height or one more. When the
right child shrinks, the same trigger instead forces `R=R'+1`; positivity
gives the old height `R'+d+2`, and the output has that height or one less.
The direct-right arguments use the corresponding `balR` laws. They do not
assume that an arbitrary annotation is invariant under tree mirroring.

Raw extraction inorder follows by induction on the original right child and
list associativity. In the ordered insertion/deletion proofs, the existing
`strict_middle` law gives child strictness and the list distribution lemmas
justify exactly the comparison-selected recursive branch. In equal-key
predecessor deletion, the raw extraction identity converts
`I l' ++ m :: I r` to `I l ++ I r`. This is the list model's result after
deleting the root, without imposing a cache or balance premise.

Ordinary AVL programs are direct specializations at `heightAnnotation` and
`d=1`. The adapters transport generic validity through `validD_one_iff` and
retain the actual height disjunctions. Cache predicates use the existing
definitional bridge. There is one recursive implementation of each operation,
with usable ordinary branch, domain, preservation and semantic equations.

## Chapter correspondence

| Canonical row | Public correspondence |
|---|---|
| C09-027 | Generic `insert` and its branch equations; ordinary `AVL.insert` specialization. |
| C09-028 | `inorder_insert`, specialized by `AVL.inorder_insert`, under strict inorder alone. |
| C09-029 | `validD_insert` and `AVL.valid_insert`, preserving the simultaneous validity/actual-height contract. |
| C09-030 | `splitMaxOption_node_nil` and `splitMaxOption_node_of_some`, with the exact source pair order and left repair. |
| C09-031 | `splitMaxOption_eq_none_iff` and `splitMaxOption_exists_of_ne_nil`; no inhabited payload. |
| C09-032 | Raw `inorder_splitMaxOption`, with separate strict/maximality observations. |
| C09-033 | `validD_splitMaxOption` and `AVL.valid_splitMaxOption`. |
| C09-034 | `delete` and its branch equations, opposite repair direction and left-maximum replacement. |
| C09-035 | `inorder_delete` and its ordinary specialization, independent of cache/balance. |
| C09-036 | `validD_delete` and `AVL.valid_delete`, including zero height change. |
| C09-055 | Existing generalized local balancers and the concrete generic update programs. |
| C09-057 | Generic insertion validity/height and strict-list semantics for every fixed positive tolerance. |
| C09-058 | Generic extraction/deletion validity/height, predecessor policy and list observations. |

The complete U01–U28 client groups exercise exact raw branch behavior, valid
duplicates/absent deletion, unordered-state separators, ordinary and generalized
single/double rotations, ties, an empty payload carrier, unchanged-height
extraction, predecessor root selection, full maximum/word summaries, zero
tolerance and the positive-integer bridge. A uniform positive-tolerance chain
family and explicit tolerance-two/three shapes supplement the universal
source theorem. The tolerance-three additions distinguish equal-child ties,
strict single rotations and both middle-child placements. Literal expected
shapes/lists/heights are paired with public theorem applications; numerical
examples alone do not establish the general contracts.

Same-height insertion and deletion are essential complete-summary consumers.
On the selected height-three tree, inserting/deleting the greatest key leaves
ancestor heights unchanged while changing both the greatest-key and inorder-word
coordinates. The new cache preservation laws justify the fresh summary; an old
summary is explicitly rejected even when its height coordinate is correct.

## Scope still open

This correspondence does not itself assert an execution or an acceptance
receipt. Exact candidate checks, complete statement inspection, independent
Spec/Standards outcomes and checkpoint publication have their recorded owners.
Receiving acceptance remains a separate integration obligation.

The ordinary/generalized [Set-by-Ordered instances](fdsa-height-set-refinement.md)
(C09-037/059) and [fixed-tolerance height theorem](fdsa-height-bound.md) (C09-061)
are later donor owners. Actual instrumented costs and logarithmic operation
bounds remain C09-039–041. Recurrence specialization here supplies only part of
C09-060; its exact cost specialization is still required. Linear construction, balance-factor algorithms,
the remaining Chapter 5 work, PFDS work and all other book/integration
requirements retain their canonical owners. No whole-book completion follows
from this bounded update family.

## Unqualified preparation for measured operation costs

C09-039–041 and the cost portion of C09-060 remain open. The following complete
operational model, proposed recurrences and separating cases were prepared by
`/root/balanced_interval_preparation` on 19 November 2026 at accepted source
`4212c4218726d47d94cfc2bcf4c53511fb2777fe`. They are **unqualified paper
preparation**, not new measured Lean programs or accepted cost theorems.
[CTB-28 and current CTB-78](../textbooks/CTB.json) retain their requirements and
receiving gate. C09-061's pure height argument has since been implemented in
[the height-bound owner](fdsa-height-bound.md); it is a prerequisite for this
still-open cost work.

The author's original 31,288-byte paper had SHA256
`1432164502247308c8581e855ad7fdaf54d03f658a3f4efe4bfed4661834fc5b`.
The primary FDSA PDF had 1,742,029 bytes and SHA256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The author visually inspected printed pages 105–112 and 116 and read the
extracted text for printed 105–116. No fresh AFP reading or compiler execution
was claimed. The event tariff below is the author's explicit model, not a
numerical count quoted from the book. This receiving curation adds no primary
reading or validation claim.

### Requirements and source correspondence

| Row | Required result and boundary |
| --- | --- |
|039|Instrument the actual cached search, insertion, extraction and deletion, including local constructors/balancers. Explicitly count root-cache access and state arithmetic/comparator tariffs.|
|040|Bound those actual traversals plus local rebuilding/rotations by input height. The predecessor-extraction path in deletion must be included. A comparison-only result is a separate observation.|
|041|Combine the ordinary exact logarithmic-height theorem with the actual operation bound. Replace node count by abstract Set cardinality only under strict search order.|
|060, cost portion|Check exact tolerance-one specialization of the measured generic recurrences. Existing value aliases/invariant adapters do not alone transport an arbitrary cost model.|
|061, now implemented|The existing generic ceiling-power and logarithmic height theorems provide the height premise. They do not prove any measured operation recurrence.|

### Actual implementation and reusable owners

`Trees.HeightBalance.HeightAnnotation α σ` has independent universes and stores
`empty`, complete `combine`, projected `height`, and the two height-algebra laws.
`ht ann t` is exactly `ann.height (Cached.read ann.empty t)`; `node ann` is exactly
the existing `Cached.smartNode`. Neither traverses a child. This fact says
nothing by itself about the internal work of an arbitrary `ann.height` or
`ann.combine` callback.

The accepted `HeightBalance.Updates` programs are important in detail:

* Insertion compares x/root, then root/x only if the first answer is false. A
  descending branch always invokes the appropriate balancer on return, even
  when the recursive value/height did not change. Its final negative/negative
  branch returns the original payload/cache/children via a raw node expression.
* `splitMaxOption nil = none`. A node with empty right child returns its whole
  left child and its own payload. Otherwise it recurses only into the nonempty
  right child and applies `balL` to the actual returned remainder.
* Deletion's descending directions use the opposite balancer. Its final branch
  executes `splitMaxOption` on the original left subtree; `none` returns the
  right child, and `some (l', m)` invokes `balR l' m r`. No second query search
  occurs inside extraction.
* `balL` and `balR` use an exact excess test `ht heavy = ht other + d + 1`, then
  a nonstrict inner comparison choosing the single rotation on a tie. They
  construct one, two or three smart nodes. Both raw missing-pattern fallbacks
  are explicit; existing lemmas prove them unreachable from correct height
  observations without requiring a balance/cache invariant.

| Existing owner / public API | Exact reuse and limitation |
| --- | --- |
|`Resources.Measured`, `bind`, `pure`, `reweight`, `bind_value`, `bind_erases`|Actual value/observation sequencing. Bind the returned measured subtree into the next measured balancer; do not rerun the unmeasured operation. Value equality alone is not cost equality.|
|`Resources.CallCount.tick`, `if_rule`, `let_rule`, `arguments_rule`|Declared additive source-event charges and selected-branch execution; these are not a compiler/runtime cost translator.|
|`Resources.TreeCache.readRun`, `nodeRun`, `nodeRun_value`, `nodeRun_cost`, `nodeRun_le`, `nodeRun_valid`|The actual callback result becomes the new annotation. Root reads cost1 each; constructor charge1; node cost is callback cost+3. No child validity is needed for the cost equation.|
|`Search.OrderedMap.lookup`, `containsKey`|The actual shared augmented search operates directly on `BinaryTree (α × σ)`. `containsKey` projects `Option.isSome`; erasure is a proof observation, not an execution. Raw source needs only decidable LT.|
|`Resources.SearchTree.lookupWithRun`|Already executes short-circuit measured Boolean comparisons, returning the actual optional annotation. Its pair records nonempty visits and comparator work. `lookupWithRun_visits_le_height`, `lookupWithRun_work_le_height`, `lookupWithRun_weighted_bound` give the required path facts. The current value-correctness wrapper is in a LinearOrder section; a minimal-LT version can be proved directly if needed.|
|`lookupRun_value`, `lookupRun_comparisons_le_height`, `lookupInspections`, `lookupInspections_le`|Existing unit-comparison specialization; failed search adds one terminal nil inspection. Raw search cost needs no ordering/cache invariant. Do not use the unbalanced `insertWithRun` as the measured AVL insertion.|
|`HeightBalance.splitMaxOption_eq_none_iff`, `splitMaxOption_exists_of_ne_nil`|Identify the actual extraction domain. The recursive right child is nonempty, so it cannot unexpectedly produce `none` after erasure correctness.|
|`HeightBalance.validD_insert`, `validD_splitMaxOption`, `validD_delete`|Already prove simultaneous full invariant and actual-height effects for every d≥1. These provide valid-state closure; they are not cost theorems.|
|`HeightBalance.balancedD_node`, `ht_eq_height_of_cacheValid`, `ht_eq_height`, `Cached.height_erase`, `numLeaves_erase`, `numNodes_erase`|Separate pure shape height from complete-cache validity and from stored-height observations.|
|`AVL.height_le_logb_numLeaves_of_valid`, `height_le_logb_numNodes_add_one_of_valid`, `height_coefficient_bounds`|Exact ordinary coefficient c=1/log₂φ, with1.440<c<1.441. Keep c, or a proved upper enclosure;1.44 is not an upper bound.|
|`AVL.ElementaryBounds`|Existing ceil-half and zero-additive logarithmic proofs demonstrate the cast/log/domain route and the floor-only inference gap. The generalized shape proof should remain independent of importing AVL.|

The source's complete word algebra is `(max hl hr + 1, leftWord ++ (a :: rightWord))`.
Appending the left word need not cost a constant. The full-annotation interface
must therefore remain general, while constant-time callback premises remain
explicit in any logarithmic operation theorem.

### A concrete, nonvacuous operational model

Use the existing `Measured value Nat` carrier, optionally with a separate
comparison-count projection. For the actual complete annotation supply:

* `heightRun : σ → Measured Nat Nat`, returning exactly `ann.height s`;
* `combineRun : σ → α → σ → Measured σ Nat`, returning exactly
  `ann.combine l a r`;
* `ltRun : α → α → Measured Bool Nat`, returning exactly `decide (x < a)`.

For the first weighted theorem assume callback work bounds H, K and C
respectively. Global bounds on height/combine callbacks are a simple sufficient
contract. Comparator bounds can instead use the existing finite-tree `All`
predicate at the two query orientations of each original payload. No comparator
is executed on an invented element. More refined reachable-callback bounds are
possible, but need their own closure proof; input-only annotation bounds do not
automatically cover newly constructed intermediate summaries.

The explicit scalar tariff is:

| Event | Charge |
| --- | ---: |
|Entry to the instrumented search/insert/split/delete operation, including its empty case|1|
|Entry to a local `balLRun` / `balRRun`|1|
|Each actual root summary read|1|
|Each executed natural addition, height equality test or height ≤ test outside callbacks|1|
|A raw nonempty tree constructor|1|
|Height projection, complete combine, payload comparison|Their actual callback observations, bounded by H/K/C when invoking the weighted theorem|
|Variables, projections, pair/Option constructors, nil construction, pattern/branch selection and wrapper aliases|0 in this declared source-event model|

`htRun` first executes `TreeCache.readRun`, then `heightRun` on its returned
summary, costing at most1+H. `nodeRun` reuses the existing complete-cache helper,
costing at most G=K+3. A raw equality-branch node has its own constructor charge1;
the fact that its value equals the input is not a physical-allocation theorem.
The model deliberately charges smart construction, root reads, height tests,
arithmetic and comparisons; it is not a comparison-only proxy.

For ordinary height annotations choose identity projection with cost0, height
combine with one unit `max` and one unit addition, and one unit per executed
strict payload comparison. Thus H=0, K=2, C=1, G=5. This node charge matches the
already checked `Examples.AVLFoundations.local_node_cost`. These units are not
bit complexity of unbounded Lean naturals, allocation bytes or elapsed time.

#### Actual decorated programs and erasure obligations

Define measured local balancers by the same two cache tests, same direct
orientations, same total pattern cases and same nested construction order as the
accepted source. Each inner measured smart node's **returned annotation/tree**
feeds its parent. Prove `balLRun_value = balL` and `balRRun_value = balR` by the
actual branch cases and `nodeRun_value`, without replacing a malformed cache by
recomputed height.

Insertion binds the actual measured child result into that measured balancer;
the equality arm emits the raw original node with charge1. Extraction binds the
actual measured recursive Option; the successful arm binds its balancer result
into `some (remainder, payload)`. Deletion binds its child or extraction result
before choosing the corresponding local repair. Prove all three value erasures
by structural induction using the existing raw equations. Extraction domain
lemmas justify the successful recursive arm where required. Retain all raw
fallbacks in the measured definition rather than dropping them on an unstated
invariant assumption.

For search, reuse the existing measured augmented lookup and project its actual
result to `isSome`; supply the chosen terminal-nil/entry tariff explicitly.
This is a measured execution of `containsKey` on the original annotated tree.
Running lookup on an eagerly erased copy would introduce an unaccounted linear
traversal. The erasure equality is useful only as a specification theorem.

### Bounded local repair, including the exact d=1 convention

The generic outer test has two `ht` calls, **two** additions (`+d`, then `+1`),
one equality test and the balancer entry. Its cost is at most6+2H. A triggered
inner test has two further `ht` calls and one ≤ test, at most3+2H.

| Actual local branch | Smart nodes | Upper cost | Ordinary exact unit cost |
| --- | ---: | ---: | ---: |
|No excess / immediate heavy-pattern fallback|1|9+2H+K|11|
|Single rotation, including equality tie|2|15+4H+2K|19|
|Double rotation|3|18+4H+3K|24|
|Middle-pattern fallback after the inner test|1|12+4H+K|14, but unreachable under the actual height laws|

Let β=18+4H+3K. Both local runs cost at mostβ on **all raw trees**, with no balance,
cache or positive-d premise. Their measured tests/callbacks must satisfy their
declared value/cost contracts. Existing heavy/middle nonempty lemmas can identify
the reachable exact branch equations, but the uniform upper bound also covers
the total fallbacks. No mirror symmetry of the full annotation is assumed.

The ordinary measured adapter should be the **same measured generic program at
`heightAnnotation, d=1`**, with the same callbacks and no extra wrapper charge.
Then its returned value and entire observation specialize exactly, by checked
equalities. Do not infer this from value equality alone. In particular:

* Normalizing the pure expression `ht r + 1 + 1` to `ht r + 2` does not preserve
  the above event count automatically. A separately instrumented literal `+2`
  version would save one declared addition per balancer invocation; prove that
  difference if such a version is exposed. The existing ordinary value aliases
  use the generic program, so the two-addition convention is the direct route.
* The book writes a three-way comparator. The actual070 program uses one or two
  short-circuit strict comparisons. Count the actual calls and state this
  convention, rather than assigning the second comparison zero invisibly.

### Actual operation recurrences and linear-height proof

Write h=t.height, I for insertion work, S for extraction work, D for deletion
work, and B for the cost of the **actual** reached local balancer. Let G=K+3,
β=18+4H+3K, A=1+2C+β. The following equations describe the proposed measured runs;
they remain proof obligations, not results of an executed cost implementation.

Insertion has `I(nil)=1+nodeCost(nil,x,nil) ≤ 1+G`. A left branch has
`1+ltCost(x,a)+I(l)+B_balL`;
a right branch has `1+ltCost(x,a)+ltCost(a,x)+I(r)+B_balR`.
The equality branch costs `2+ltCost(x,a)+ltCost(a,x)` (entry and raw constructor).
Always use the returned recursive tree in B; its shape/cache may differ from
the input child's. Since the uniform local bound is independent of that shape,
structural induction proves

`I(x,t) ≤ A * h + (G+1)`.

Extraction has S(nil)=1 and S(node a l nil)=1. When the original right child r
is nonempty, its actual success and remainder r' give

`S(node a l r) = 1 + S(r) + B_balL(l,a,r')`.

It does **not** recurse into the terminal empty right child. Prove the useful
strengthened statement `t ≠ nil → S(t) ≤ (β+1)*h`, and the uniform statement
`S(t) ≤ (β+1)*h+1`. For a nonempty extraction path with v reached nodes, there
are exactly v operation entries and v−1 balancer calls. This exact path/count
lemma distinguishes extraction from a search that examines a terminal nil.

Deletion's left/right descending arms add an entry, one/two actual payload
comparisons, the recursive cost and one balancer. Its equality arm costs

`1 + ltCost(x,a) + ltCost(a,x) + S(l)
   + (if the actual extraction succeeds then B_balR(l',m,r) else 0)`.

Prove `D(x,t) ≤ A*h+1` by structural induction, using the extraction bound first.
At equality, `S(l) ≤ (β+1)*h_l+1` and `h_l+1≤h`; therefore the arm is at most
`(β+1)*h_l + β + 2C + 2 ≤ A*(h_l+1)+1 ≤ A*h+1`.
This also bounds the empty-left case, whose exact cost is smaller. At a
descending arm, the induction hypothesis plus at most1+2C+β=A fits one further
original level. Thus the search prefix and predecessor path are charged as one
continuation through the original input, not as unrelated full-height searches
at every ancestor. No rotation output-height premise is necessary for this
input-path bound: recursion proceeds into an original child before repairing.

More explicitly, if deletion reaches its matching node after p original
ancestors and its nonempty left predecessor path visits v nodes, then
`p+1+v ≤ h`. There are p+v balancer calls: one at each search ancestor, v−1
inside extraction, and one at the matching node. If the left child is empty,
the explicit `splitMaxOption nil` contributes its entry even though it returns
none; total operation entries are still at most h+1. An absent-key search also
has at most h nonempty entries, one terminal nil entry and h balancer calls.
These literal path identities are useful strengthenings of the induction,
and distinguish an empty extraction call from a nonempty extraction's base node.

Search with the terminal-empty charge has
`Q(x,t) ≤ (1+2C)*h+1`, by the existing visit/comparator bounds. A comparison-only
projection for insertion/deletion can equal the corresponding lookup count,
because all rotations happen after the search descends and extraction makes no
payload comparisons. That result is useful but does not include rebuilding or
height tests; it must not replace the whole-work bound.

For the stated ordinary units (H=0,K=2,C=1), the explicit sufficient bounds are:

`Q ≤ 3h+1`, `I ≤ 27h+6`, `S ≤ 25h+1`, `D ≤ 27h+1`;
for nonempty extraction, `S ≤ 25h`.

These bounds hold for raw inputs under the callback contracts; balance/order
is not needed to bound work by **actual input height**. Validity becomes relevant
when replacing height by a logarithm or preserving a valid sequence of states.

### Ordinary logarithmic operations and the empty case

For an ordinary valid t, reuse
`h ≤ c * log₂ L`, where c=1/log₂φ and L=t.numLeaves=t.numNodes+1.
For example the proposed full insertion bound becomes

`I(x,t) ≤ 27*c*log₂(t.numNodes+1) + 6`,

and deletion becomes the same coefficient with additive1. Search has coefficient
3c and additive1, extraction coefficient25c and additive1 (or none for its
nonempty domain). Cast the proven Nat cost bounds to reals and multiply the
existing height bound by nonnegative constants. Do not round c down to1.44.

The additive terms matter: nil has h=0 and L=1, so log₂L=0 while insertion costs6
and the chosen empty search/extraction/deletion each cost1. The uniform
pointwise statement is affine in log, or O(1+log(n+1)). For an asymptotic family
indexed by n≥1, log₂(n+1)≥1 absorbs the additive term and yields the usual
O(log(n+1)); state fixed callback bounds and fixed tolerance at every index.
`Resources.Growth.clog_two_cast_le_two_logb` illustrates the real-log domain
and slack bookkeeping, but its existing `isBigO_of_clog_two_bound` concludes
O(n log n), not the desired O(log(n+1)). The latter affine-log-to-BigO bridge
must be proved with the stated eventual n≥1 domain, not imported under the
wrong growth target.

Only strict order (the Set representation predicate S) licenses equality of
node count and abstract cardinality. Valid cache/balance alone permits duplicate
payloads: arbitrarily large perfect trees of one repeated key have Set
cardinality1. The existing C09-037/059 Set refinement supplies the strict-order representation
condition. The node-count/cardinality equality still needs its own proved bridge;
it does not follow merely from naming that refinement. No cardinality bridge is needed for a node-count theorem.

### Existing fixed-tolerance height premise

The completed shape owner proves, for every natural d, including zero, arbitrary
payload universes and recursively `BalancedD d` trees:

`2^((height+d)/(d+1)) ≤ leaves`,
`height ≤ (d+1) * log₂(leaves)`, and
`height ≤ (d+1) * log₂(numNodes+1)`.

Its threshold induction uses both child inequalities and its quotient/remainder
argument proves the ceiling rounding. Complete-cache adapters distinguish actual
height from stored height; the latter uses an actual cache-correctness premise.
The positive-integer bridge retains both positivity and exact coercion back to
the supplied integer. The ordinary sharper golden-ratio bound remains separate.
See [the complete argument and cases](fdsa-height-bound.md).

Once the measured input-height bound above is proved, substitution gives, for
fixed d and callback bounds, `I ≤ A*(d+1)*log₂(numNodes+1)+(G+1)`. This is still
an unproved cost consequence. If d grows with input size, its coefficient grows:
ordered chains of height n are d-balanced for d≥n−1 and have linear search paths.
No uniform logarithmic constant independent of d follows.

### Optional minimum recurrence, still unqualified

A sharper route could define F_d(0)=1 and
`F_d(h+1)=F_d(h)+F_d(h-d)` with truncated natural subtraction. A Unit-labelled
witness follows the same recursion with child heights h and h-d, giving actual
height h+1 and balance difference at most d. Monotonicity and induction then
yield the exact minimum-leaf interpretation. For1≤h≤d+1 it has F_d(h)=h+1;
at d=1 it is the familiar shifted Fibonacci sequence. This is consistent with
the canonical ledger's attributed AFP description, but this author did not
freshly read AFP. Proving its optimal characteristic root, asymptotic formula
or exact minimum is unnecessary for the book's fixed-d logarithmic claim.

### Discriminating expected cases for later independent adoption

These are author-derived paper expectations, not newly independent review
results and not executed tests. The exact cost numbers below use precisely the
the declared scalar tariff units and the current generic two-addition syntax.

| Case | Expected result / reason |
| --- | --- |
|Empty search / insertion / extraction / deletion|Costs1 / 6 / 1 / 1; output erasures match the real empty equations. Catches missing base work and an impossible zero-additive operation bound at log1=0.|
|Singleton hit, smaller miss, greater miss in search|Costs3,3,4. The second comparison executes only after a false first answer; missing search includes terminal nil.|
|Duplicate insertion into a singleton|Cost4, exact raw identity and no smart-cache repair. Still charge the raw constructor under the selected model; do not infer no physical allocation.|
|Smaller/larger insertion into a singleton, d≥1|Costs19/20: empty insertion6 plus one no-trigger balancer11, operation entry and one/two comparisons. Both returned nodes must use the actual measured child.|
|Absent smaller/larger deletion from a singleton|Costs14/15 although the resulting tree equals the input. It still recurses to nil and rebuilds through the actual local balancer.|
|Local fallback/single-tie/double repair|Ordinary reachable costs11/19/24; two versus three smart constructors and two versus four cache-height reads distinguish branches. Both direct orientations must be covered.|
|Nil versus singleton extraction|Both cost1, but one returns none and the other some(nil,payload). Extraction does not inspect a terminal nil by a recursive call.|
|Extraction from a perfect three-node tree|Cost13: two extraction entries and one no-trigger balancer. Returns the original greatest/rightmost payload with a correctly rebuilt remainder.|
|Delete root4 from perfect seven|Cost27: one deletion entry, two payload comparisons, extraction cost13 and final no-trigger repair11. A comparison-only account would miss most work. Result uses predecessor3.|
|Equal-height deletion tie|Single rotation costs19 and may preserve actual height; do not skip recomputation or a constructor because height did not decrease. Reuse the retained literal U20/U23 trees.|
|Same-height maximum/word update|Both ancestors' complete summaries must change. Returning a height-only reconstruction fails erasure even if its height and branch costs look plausible.|
|Unbounded word callback|A large left subtree forces linear list-append work at one root combine. No uniform constant K, hence no unconditional generic full-summary logarithmic-time theorem.|
|Malformed stored height|The raw run follows forged cache tests; measured erasure must agree with that actual behavior. Its cost can remain height-linear, while stored-height/log or validity conclusions fail.|
|Empty pure shape and one-node shape|Leaves1/2, height0/1; ceil exponent0/1. The real-log domains and empty case are exact.|
|d=0 balanced shapes|Perfect shapes satisfy leaves=2^h; the pure generalized height theorem still holds. This does not validate d=0 update preservation.|
|d=2, h=3 chain|Leaves4 and balance tolerance2; ceil bound2≤4. It is not ordinary AVL. At h=4, the candidate minimum recurrence gives6 leaves, exceeding the ceil lower bound4.|
|Floor-only arithmetic gap|For q≥2 choose numerical h=q+1,L=2:2^floor(h/q)≤L but h>q*log₂L. This pair is an arithmetic separator, not a claim that a balanced tree has those measures.|
|d varying with n / duplicate-key size|An ordered chain with d≥n−1 defeats a d-independent log constant. A large balanced duplicate-key tree defeats replacing node count by Set cardinality without S.|

### Failed approaches and concrete remaining work

The following tempting routes are rejected for mathematical reasons, not because
of an observed compiler failure (no compiler was run in this task):

1. Giving a pure update its already-known height bound as an attached cost, or
   reusing the unbalanced insertion run wholesale, would measure a proxy. Bind
   the real local measured callbacks and prove value erasure branch by branch.
2. Recursively recomputing height in a balancer changes the algorithm. A single
   top-level height traversal of a large balanced subtree already costs linear
   nodes, despite logarithmic height.
3. Assuming arbitrary complete combines are constant-time is false for words;
   replacing them by height-only construction changes the returned value.
4. Counting comparisons alone misses every smart construction and the
   predecessor extraction; counting two independent searches at every ancestor
   invents work the actual recursion never executes.
5. Assuming an update with unchanged height costs zero misses mandatory ancestor
   rebuilding and complete-summary changes, including deletion ties.
6. Value normalization `+1+1=+2`, or equality of pure ordinary/generic values,
   does not prove exact observation equality. Keep the measured d=1 alias or
   prove its explicit overhead relation.
7. A floor-only exponential bound does not imply the zero-additive height/log
   inequality. The threshold induction plus quotient/remainder argument supplies
   the needed ceil strength.
8. A generic optimal-root/AFP port is possible but adds unnecessary analytic
   obligations for061. The direct q-block proof is sufficient and keeps all
   domains and constants explicit.

### Remaining implementation

Reuse the completed pure shape/height and Set-refinement owners. Still implement
the actual measured cache and direct local-balancer programs with returned-value
sequencing; prove their erasures, branch costs and the uniform β bound. Then
implement the measured insert/extract/delete/search recurrences, the stronger
nonempty extraction bound, exact ordinary specialization, height/log consequences
and the cases above. A separate comparison-only observation may reuse the search
path proof, but cannot replace complete work accounting. The optional minimum
recurrence remains paper preparation and is not required for C09-061.

None of this changes existing source qualifications or establishes receiving
acceptance, wall-clock, bit-cost, allocation or physical-sharing results.
