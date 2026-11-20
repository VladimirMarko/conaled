# Cached local rebalancing with a complete height annotation

The generic owners are `Applications/Trees/HeightBalance/Basic.lean` and
`Applications/Trees/HeightBalance/Rebalance.lean`. The ordinary specialization
is `Applications/Trees/AVL/Rebalance.lean`; connected applications are in
`Examples/HeightRebalance.lean`. This bounded increment addresses exactly
**C09-018–026, C09-038, C09-054 and C09-056**, under local CTB-118 and the unchanged
CTB-28 Chapter 9 owner. Canonical obligations remain in
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`.

The source is Tobias Nipkow's *Functional Data Structures and Algorithms*,
July 27, 2026 edition, printed pages 107–112 (physical pages 113–118). Its exact
PDF SHA256 is `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The official [PDF location](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
is mutable, so the hash identifies the edition. The independent case author `/root/rebalance068_cases_recovery` read the
extracted text and visually inspected all six pages on19 November 2026. The
expectations restate an earlier 20,399-byte independent local-balancer paper
(SHA256 `fff78d4e55c9f801478ecedbc9858c39f9fcfb737f6b5b32093b0a7c3242e88c`),
whose original canonical agent name was not recorded. No fresh visual reading
is claimed by this receiving curation. The complete useful cases and actual
declaration mapping are now below, rather than dependent on a recovery wrapper.

## Shared representation and complete summaries

The carrier is the existing `BinaryTree (α × σ)`, with arbitrary independent
payload and annotation universes. `HeightAnnotation α σ` supplies `empty`,
`combine : σ → α → σ → σ`, and `height : σ → Nat`, with exactly two laws:

\[
\operatorname{height}(\operatorname{empty})=0,\qquad
\operatorname{height}(\operatorname{combine}(L,a,R))
=\max(\operatorname{height}(L),\operatorname{height}(R))+1.
\]

The annotation may also contain maxima, ordered words or other data. The
generic interface requires no order, equality decision, inhabitance,
associativity, commutativity or mirror symmetry. Its `ht` applies the height
observation to the stored root summary using `Trees.Cached.read`; `node` is the
existing `Cached.smartNode` with the complete algebra. It reads child roots
and recomputes the whole new summary, retaining the child trees.

`CacheValid` is existing recursive `Cached.Valid`. `BalancedD d` concerns only
the actual shape and, recursively, requires both natural inequalities
`hl ≤ hr+d` and `hr ≤ hl+d`. `ValidD` combines that erased-shape predicate with
complete recursive cache correctness. A correct root height, or even a correct
root summary, does not establish correctness of retained descendants.

The stored-to-actual-height bridge follows the existing fold laws.
`Cached.read_eq_fold` identifies a cache-valid stored summary with the complete
fold. `Trees.fold_fusion` transports that fold through the height observation,
and `Trees.fold_height` identifies the resulting natural fold with structural
height. `Cached.height_erase` finishes the bridge. Balance is unnecessary.

`validD_node_iff` characterizes a raw node by validity of both children, the
signed actual-height inequality, and equality of the **entire** stored summary
with `combine (read l) a (read r)`. `node_validD_iff` removes only the independent
root equation because smart construction computes it. The ordinary Nat instance
also exposes the exact actual-child-height form of this equation.

The signed condition is proved equivalent to the two natural inequalities:

\[
|(h_l:\mathbb Z)-(h_r:\mathbb Z)|\le(d:\mathbb Z)
\quad\Longleftrightarrow\quad h_l\le h_r+d\land h_r\le h_l+d.
\]

Casts occur before subtraction. For example, integer `0−3` has absolute value
three, whereas `(0−3 : Nat)` is zero. The lower-range bridge
`hr−d ≤ hl ↔ hr ≤ hl+d` uses truncated natural subtraction, including `hr<d`.
For an integer tolerance `D≥1`, `int_tolerance_toNat` proves both positivity of
`D.toNat` and exact cast equality before the integer statement is transported.
The negative integer case is not silently identified with natural tolerance zero.

## Exact raw programs

Write `n(L,a,R)` for the complete smart node and `N((a,s),L,R)` for a raw node.
Both programs test exact equality of stored projected heights. A larger
imbalance does not satisfy the trigger merely because it exceeds the threshold.

| Program and branch | Exact output |
| --- | --- |
| `balL ann d l a r`, when `ht l ≠ ht r+d+1` | `n(l,a,r)` |
| Left trigger, `l=N((b,s),A,B)`, `ht B≤ht A` | `n(A,b,n(B,a,r))` |
| Left trigger, strict inner dominance, `B=N((c,t),P,Q)` | `n(n(A,b,P),c,n(Q,a,r))` |
| `balR ann d l a r`, when `ht r ≠ ht l+d+1` | `n(l,a,r)` |
| Right trigger, `r=N((c,s),B,C)`, `ht B≤ht C` | `n(n(l,a,B),c,C)` |
| Right trigger, strict inner dominance, `B=N((b,t),P,Q)` | `n(n(l,a,P),b,n(Q,c,C))` |

Equality in the inner/outer comparison selects the single rotation. The raw
missing-heavy and missing-middle patterns are unreachable from their guards:
an empty tree reads height zero, so it cannot have height `short+d+1` or be
strictly taller than another natural height. These domain laws hold for every
natural tolerance, including zero, and need no cache or balance premise.
The total definitions require no invented payload for an impossible branch.

The right program is separately oriented. Plain mirroring retains annotation
values and need not commute with a complete algebra. Reversing only numerical
height variables in arithmetic lemmas does not assert such an annotation law.

`inorder_balL` and `inorder_balR` hold on every raw input, including incorrect
caches, repeated labels and unsorted contents. The observation is the ordered
payload list after erasing annotations; it is not the list of old payload-cache
pairs. Every newly built node computes its complete summary, and
`cacheValid_balL/R` preserve full recursive cache correctness from cache-valid
children for every natural tolerance.

## Height effects and full repair have different hypotheses

The actual-height results use cache correctness to connect executable stored
guards to structural heights. Under `d≥1` and the actual trigger, the output
height is `short+d+1` or `short+d+2`. Child shape balance is unnecessary for this
height conclusion. A single rotation with equal inner and outer heights gives
the larger value; strict single and double rotations give the smaller one.
For a cache-correct non-trigger input, actual output height is simply
`max hl hr+1`, without any positivity or balance-range premise.

Full recursive repair has the stronger hypotheses. For `balL`, both input
children must satisfy `ValidD` and the allowed range is

\[
h(r)-d\le h(l)\le h(r)+d+1.
\]

For `balR`, exchange the roles of left and right. These ranges include the
extra-level repair case and the opposite-side boundary. In a non-trigger case,
natural arithmetic reduces the allowed range to the usual two-sided tolerance.
In a rotation case, child validity supplies the descendant balance facts needed
at the newly assembled nodes. Cache preservation supplies the entire summary
invariant independently.

Tolerance zero is excluded from this repair theorem for a mathematical reason.
With a singleton heavy child and empty short child, the raw zero-tolerance
trigger holds and the tie selects a single rotation. The resulting two-node
tree has a root gap of one, so it is not zero-balanced. The raw domain, inorder
and cache laws remain valid there.

## The stronger double-rotation diagram

For a left double rotation let the outer height be `x`, middle child heights be
`p,q`, short height be `k`, and `d≥1`. The public
`double_rotation_height_bounds` assumes

\[
\max(x,\max(p,q)+1)+1=k+d+1,\quad
x<\max(p,q)+1,\quad \max(p,q)+1\le x+d.
\]

It proves `max(p,q)+1=k+d`, `k≤x`, and `x+1≤k+d`. The two new child heights
`L=max(x,p)+1` and `R=max(q,k)+1` satisfy

\[
k+1\le L,R\le k+d,\qquad \max(L,R)=k+d,
\qquad L\le R+(d-1),\quad R\le L+(d-1).
\]

Strict inner dominance gives the middle maximum. Heavy-root balance gives the
lower bound on the outer height. One middle grandchild attains its maximum,
so one rebuilt child attains `k+d`; both lie in an interval of width `d−1`.
The middle child's own balance is unnecessary for these height conclusions.
It remains necessary for a conclusion of complete recursive balance: the case
`d=2,k=2,x=3,p=0,q=3` satisfies this height diagram and gives new heights `4,4`,
while a rebuilt child has gap `3>2`.

At `d=1`, the ordinary adapter derives outer height `k`, middle maximum `k`,
and the disjunction that at least one middle grandchild reaches `k`. Both may
reach it, but both need not. The tagged cases cover left-only, right-only and
both, including the payload list `[1,2,4,5,6,7]`. For `d>1`, the new child
heights can differ: tolerance three admits the pair `3,1`, attaining gap two.
The right double diagram uses `L=max(k,p)+1`, `R=max(q,x)+1`; payload positions
remain in their actual right-oriented order.

## Ordinary AVL and connected augmentation cases

`Trees.AVL.heightAnnotation` uses the existing `heightCombine` with identity
projection. Exact reader, smart-node and recursive-cache bridges connect it to
the earlier AVL owners. `balancedD_one_iff` and `validD_one_iff` establish the
shape and complete-invariant equivalences. Ordinary `balL` and `balR` are these
actual generic programs at tolerance one. Their public branch equations use
the source's literal `+2` trigger, with ordinary inorder, cache, height and
full-range validity laws transported through the checked bridges.

The independent R01–R35 expectations cover both raw programs and the separate
premise layers: empty input, single ties, all tagged double placements, raw
cached/actual disagreements, exact equality versus a threshold, retained bad
descendants, unordered duplicates, generalized range boundaries, tolerances two
and three, wrong-tie failures, height-only versus balance conclusions, signed
arithmetic, negative tolerance and zero-tolerance failure. E01 instantiates an
empty payload type with no global inhabitance requirement. The complete case
body and actual declaration crosswalk are preserved below.

A01 uses `Nat × Option Nat` and the actual `Trees.MaximumCache.combine`.
Repairing the left subtree containing keys one and two above pivot nine gives
root summary `(2,some 9)`. Retaining the promoted root's old `(2,some 2)` gives
the same shape, projected height and inorder but an invalid complete cache.
The client's maximum observation composes cached-fold correctness and fold
fusion with the existing maximum-summary semantics. Maximum order assumptions
belong to this application, not to the generic rebalancer.

A02 uses `Nat × List Nat`, combining ordered words as `left ++ pivot :: right`.
The direct right program returns a valid root summary `(2,[1,2,3])`. Plain
mirroring keeps this annotation while changing actual inorder to `[3,2,1]`.
More strongly, mirroring the result of a left repair on mirrored input leaves
the wrong word `[3,2,1]` on the direct right result's shape. Full cache validity
and the separately oriented right theorem distinguish these computations.

## Independent case crosswalk

The independent expectations below were prepared before implementation.
Their subsequent actual declaration connections are listed after the cases.
This receiving curation confirms named-source presence, not a fresh elaborated
dependency audit or receiving pass. Raw counterexamples remain separate from
premise-satisfying applications of validity theorems.

Notation: E is nil. `N[a;s](L,R)` is a raw node; `n(L,a,R)` is the complete smart
node. For height-correct examples, `N_a(L,R)` abbreviates that smart node.
`leaf a = N_a(E,E)`. `P_h` denotes a correctly annotated perfect shape of height
h (P0=E); every such shape is d-balanced for all d. Labels of different P_h
subtrees need not be ordered or distinct unless a concrete inorder is given.
Actual height is h(t), stored projected height is ht(t), and I(t) is payload
inorder after erasure. Numeric tuples below are actual heights, not caches,
unless explicitly marked raw.

### Ordinary and raw cases

| ID | Exact input / expected result | Public contract distinguished |
|---|---|---|
| R01 | d=1, l=r=E, pivot 2. Both balancers return leaf 2, height 1, complete valid cache, inorder[2]. | Non-trigger equation, ordinary adapter, validity. |
| R02 | balL `N_2(leaf1,E)` 3 E returns `N_2(leaf1,leaf3)`, height 2, inorder[1,2,3]. Heavy height 2, short 0, inner 0<outer 1. | Exact left strict single; lower height alternative. |
| R03 | balL `N_2(leaf1,leaf3)` 4 E returns `N_2(leaf1,N_4(leaf3,E))`, height 3, inorder[1,2,3,4]. The heavy inner and outer heights are both 1. | Equality selects single and preserves the unbalanced parent height 3. |
| R04 | balL `N_2(leaf1,N_4(leaf3,E))` 6 leaf 7 returns `N_4(N_2(leaf1,leaf3),N_6(E,leaf7))`, height 3, inorder[1,2,3,4,6,7]. Here (k,x,p,q)=(1,1,1,0). | Left double with only the left middle grandchild reaching k; payload placement, balanced children 2/2. |
| R05 | balL `N_2(leaf1,N_4(E,leaf5))` 6 leaf 7 returns `N_4(N_2(leaf1,E),N_6(leaf5,leaf7))`, height 3, **inorder[1,2,4,5,6,7]**. Here (k,x,p,q)=(1,1,0,1). | Left double with only the right middle grandchild reaching k. Preserves the recovered O05 payload-order correction. |
| R06 | balL `N_2(leaf1,N_4(leaf3,leaf5))` 6 leaf 7 returns `N_4(N_2(leaf1,leaf3),N_6(leaf5,leaf7))`, height 3, inorder[1,2,3,4,5,6,7]. Here (k,x,p,q)=(1,1,1,1). | Both middle grandchildren can reach k; neither exclusivity nor both-reaching necessity is valid. |
| R07 | balR leaf 1 2 `N_6(N_4(P,Q),leaf7)`, where (P,Q) is respectively (leaf 3,E), (E,leaf 5), or (leaf 3,leaf 5), returns `N_4(N_2(leaf1,P),N_6(Q,leaf7))`. Each result has height 3; inorders are respectively [1,2,3,4,6,7], [1,2,4,5,6,7], [1,2,3,4,5,6,7]. | All three directly oriented right-double cases, with exact subtree and pivot order. |
| R08 | balR E 1 `N_2(E,leaf3)` returns `N_2(leaf1,leaf3)`, height 2, inorder[1,2,3]. | Right strict single and lower height alternative. |
| R09 | balR E 1 `N_3(leaf2,leaf4)` returns `N_3(N_1(E,leaf2),leaf4)`, height 3, inorder[1,2,3,4]. | Right tie single and higher height alternative. |
| R10 | For every natural d and all raw r, ht(E)=0 cannot equal ht(r)+d+1. The right analogue is identical with the roles swapped. | Heavy-child domain, with no cache validity or d≥1 premise. |
| R11 | For arbitrary raw outer A, a strict double guard ht(A)<ht(E)=0 is impossible; the right-oriented counterpart also holds. A positive cached middle height forces a node even when its annotation is wrong. | Middle-child domain without cache/balance/inhabitance assumptions. |
| R12 | Raw l=`N[1;2](E,E)`, pivot 2, r=E, d=1. The stored trigger is true and both child caches are 0, so single returns `N_1(E,leaf2)`, actual height 2 with a valid complete height cache and inorder[1,2]. The malformed heavy root is discarded. | Cached rather than actual trigger; cache correctness of an output can improve when the bad root is removed. No converse validity claim. |
| R13 | Change only R12's stored heavy root to3. Trigger 3=2 is false, so fallback returns `n(l,2,E)` with stored root 4, actual height 2, inorder[1,2], and invalid recursive cache. | Exact equality, not ≥2; a wrong root remains when retained as a child. |
| R14 | Raw l=`N[1;2](E,N[2;0](E,E))`, pivot 3, r=E. Cached inner and outer heights both 0 choose single, although actual inner height 1 exceeds actual outer 0. Output is `n(E,1,n(N[2;0](E,E),3,E))`, actual height 3, inorder[1,2,3], and invalid cache/shape balance. | Single tie is a comparison of stored heights. Actual-height branching would be a different raw program. |
| R15 | Raw l=`N[2;0](leaf1,E)`, pivot 3, r=E. Actual left height 2 is a +2 imbalance, but its stored 0 fails the trigger. Fallback has actual height 3 and stored root 1; inorder[1,2,3] still holds. | Cache premise is necessary to translate actual triggers and actual fallback height through ht. |
| R16 | Raw T=`N[2;2](N[1;0](E,E),leaf3)`. The root cache 2 equals both actual height 2 and max(stored child heights)+1, but the left leaf is invalid. Full CacheValid T is false. | Checking only the root's equation or only actual root height is insufficient. |
| R17 | balL T 4 E with T from R16 takes the cached double branch and yields `n(n(N[1;0](E,E),2,E),3,leaf4)`. It retains the bad leaf; actual root height 3 but stored projected root 2. Inorder[1,2,3,4] holds and recursive cache validity fails. | Rebuilding new nodes does not repair an untouched invalid descendant. |
| R18 | In R02 replace labels (outer 1,heavy 2,parent 3) by (9,9,2). Output is `N_9(leaf9,leaf2)` and both input-parent and output inorder are [9,9,2]. | Unconditional inorder retains duplicates and unsorted order; no search/set premise is hidden. |
| R35 | Raw l=`N[b;2](P2,E)`, pivot a, r=E, d1. Actual left height 3 is not the exact +2 trigger, but stored 2 selects single. The result `n(P2,b,leaf a)` has actual height 3, whereas max(actual left 3,right 0)+1=4. | A cache-validity premise is necessary for the fallback height law stated from absence of the actual trigger. This adds a sharper separator than simply observing an incorrect stored root. |

R12–R17 and R35 are deliberately malformed. They are raw semantic/domain examples, not
premise-satisfying uses of a ValidD preservation theorem. For any raw malformed
case, the payload inorder may agree while the inorder of (payload,old-cache)
pairs changes; the public equation is for erased payloads.

### Generalized range, height and hypothesis cases

| ID | Exact input / numerical expectations | Distinction and inherited origin |
|---|---|---|
| R19 | For every d≥1, left-domain boundary pairs (hl,hr)=(0,d), (d,0), (0,0) take fallback and are d-balanced at the new root, with heights d+1, d+1,1. Pair(d+1,0) triggers repair. Reflect all four pairs for balR. Children can be P_h. | Both range boundaries and empty lower truncation; inherited B01, B06. |
| R20 | d=1, cache-valid P3 versus E has heavy difference 3, so balL fallback has height 4 and valid cache but is unbalanced. Separately, a triggered single with short=P2 (k2), outer=P3, inner=E has heavy height 4 and produces height 4=short+2, but the rebuilt inner node has gap 2>1. Mirror both inputs for balR. | Exact trigger is not an arbitrary imbalance repair; cache-only height alternatives need no child balance. B01/B08, with fresh explicit witnesses. |
| R21 | For d≥1, balL E a P_(d+1) has valid children but violates the opposite-side bound; it takes fallback and the root gap d+1 is invalid. Mirror with balR P_(d+1) a E. | Neither one-sided lower bound may be omitted. |
| R22 | Short k0, heavy outer P_d and inner E. Triggered single has result child heights(d,1), result height d+1, versus original parent d+2. For d2 the children are 2/1; for d3 they are 3/1. Mirror directly. | General strict-single arithmetic, B02/B06. |
| R23 | Short k0, outer=inner=P_d. Tie single has result children(d,d+1), result height d+2, equal to the original parent. Right tie has children(d+1,d). | Equality must select single and keep the high alternative, B03/B06. |
| R24 | For d3,k0, outer 3 and inner s=0,1,2,3 give single result child pairs(3,1),(3,2),(3,3),(3,4) and heights 4,4,4,5. For d2, s=0,1,2 gives(2,1),(2,2),(2,3) and heights 3,3,4. | Intermediate heights as well as endpoints; not a d1/d2-only argument. The general formula proves all s, these rows discriminate it. |
| R25 | For every d≥1 choose k1, outer=P_(d+1), inner=N_b(E,P_d), and short=P1. Heavy outer/inner heights tie at d+1; all supplied children can be d-valid. The correct single remains valid. An incorrectly forced double creates a child with heights(d+1,0), which is not d-balanced. Mirror with the correspondingly reversed middle child. | A uniform counterexample to replacing ≤ by < in the single guard; inherited B04/B06. |
| R26 | d2,k0,x0 and middle(p,q)=(1,0),(0,1),(1,1) produce double child pairs(2,1),(1,2),(2,2), result height 3. d3,k0,x0 and (p,q)=(2,0),(0,2),(2,2) produce(3,1),(1,3),(3,3), result height 4. | Each maximal-middle position and simultaneous maximum; gap d−1 is attained and child heights need not agree for d>1, B05/B11. |
| R27 | Right double uses L=max(k,p)+1 and R=max(q,z)+1. With z=k=0, the same pairs in R26 give the same listed pairs. With d3,k0,z1,p0,q2, the pair is(1,3), not the left-formula pair(2,3). Result height 4, input child validity holds. | A directly oriented generalized witness that detects copying the left formula without swapping positions. |
| R28 | d2,k2,x2,p1,q3: heavy height 5, short 2, strict inner 4>outer 2. Double children are 3/4, result 5. The middle minimum p=k−1 is allowed. The component subtrees may be P_h, giving valid supplied children. | Positive-k lower middle boundary, natural subtraction; inherited double derivation. |
| R29 | Choose d2,k2,x3,p0,q3. Heavy root heights 3/4 are locally within d2, and the height diagram gives new children 4/4 and result 5. The middle node has child heights 0/3 and is not d-balanced. The new left node has child heights 3/0 and also fails d2 balance. | The stronger height diagram remains true without middle-child balance, while complete recursive repair can fail. No ValidD theorem may be applied to this input. |
| R30 | For naturals hr,d, `hr−d≤hl` iff `hr≤hl+d`. Example hr0,d3,hl0 has truncated lower bound 0. In contrast, hl0,hr3,d1 violates the two-sided balance test. | Exact natural-subtraction range transport; no hidden assumption d≤hr. |
| R31 | hl0,hr3,d1: `abs((0:Int)−(3:Int))=3>1`, while `abs(((0−3:Nat):Int))=0≤1`. For hl3,hr0 the truncation loses no information, demonstrating why checking one sign is insufficient. | Explicit cast-before-subtraction counterexample; use the displayed Nat type annotation in a formal client. |
| R32 | For every natural d, signed abs((hl:Int)−(hr:Int))≤(d:Int) iff hl≤hr+d and hr≤hl+d. For integer D≥1, d=D.toNat has d≥1 and (d:Int)=D; hence the literal integer-d formulation transports. | General bridge, not an unchecked cast or restriction to fixed examples. |
| R33 | D=−1 and equal child heights 0 give abs difference 0≤−1 false, whereas D.toNat=0 would accept the local two-sided natural test. | Positivity/nonnegativity is necessary when recovering an integer tolerance from toNat; inherited negative-tolerance separator. |
| R34 | d0, l=leaf 1, r=E, pivot 2. Both supplied children are 0-valid and exact trigger 1=0+0+1 holds. Tie single returns `N_1(E,leaf2)`, whose root gap is1, so it is not 0-balanced. Raw inorder/domain/cache laws still apply. | The d≥1 premise of repair is substantive, inherited B10. |

For R25's reflected wrong-tie witness, reverse the middle children as part of
the orientation change: with right-heavy outer P_(d+1), middle=N_b(P_d,E), and
short P1, the wrongly rebuilt right child has heights 0/(d+1). Reflection here
describes heights/shapes for choosing a mathematical example, not a theorem
that arbitrary full annotations commute with mirror.

### A01: complete height × optional-maximum annotation

Use payload Nat, σ=Nat×Option Nat, empty=(0,none), height=Prod.fst, and
`combine L a R = (max L.1 R.1 + 1, Trees.MaximumCache.combine L.2 a R.2)`.
This uses the actual existing maximum algebra, not a new ad hoc maximum.

Take left `n(leaf1,2,E)`, parent 9 and right E, at d1. The heavy root stores
(2,some 2). Correct balL returns `n(leaf1,2,leaf9)`, whose child annotations are
(1,some 1) and (1,some 9), and whose complete root is **(2,some 9)**. Actual
height 2 and inorder[1,2,9] are immediate observations. Retaining the promoted
root's old maximum would instead produce raw root **(2,some 2)** over exactly
those children. That tree has the same erased shape, actual height, projected
height and payload inorder, yet fails `Cached.Valid` because the combine is
(2,some 9). Thus a height-only update can pass every height test while losing
the intended augmentation.

The direct right counterpart balR E 1 `n(E,2,leaf9)` returns the same complete
tree `n(leaf1,2,leaf9)`. Its intended proof consumers are the **generic** direct
right branch, inorder and cache/ValidD laws, not a height-only AVL theorem.

For semantic maximum correctness, project the complete fold through Prod.snd,
prove the empty/combine projection equations, use `Cached.read_eq_fold` and
`Trees.fold_fusion`, then reuse existing
`Trees.MaximumCache.summary_eq_max?_inorder`. Its companion
`summary_eq_some_iff` retains both attainment and upper-bound meaning. No bottom
element or default label is needed. The generic balancer itself needs no
LinearOrder; this Nat maximum client supplies the required order only where
the maximum meaning is asserted.

### A02: complete height × ordered-word annotation

Use payload Nat, σ=Nat×List Nat, empty=(0,[]), height=Prod.fst, and
`combine L a R = (max L.1 R.1 + 1, L.2 ++ a :: R.2)`.
This is ordered and noncommutative. Correct right repair
balR E 1 `n(E,2,leaf3)` yields `n(leaf1,2,leaf3)` with root (2,[1,2,3]),
child summaries (1,[1]) and (1,[3]), payload inorder[1,2,3], and full validity.
The left repair of `n(leaf1,2,E)` with parent 3 also yields that tree.

Plain tree mirror exchanges children while retaining every annotation. If T
is this valid root 2 tree, mirror T still stores root word[1,2,3], but its actual
inorder is [3,2,1]; the correct root summary is (2,[3,2,1]). Thus mirror T is
not fully cache-valid, although projected heights remain correct. Recomputing
the mirror with the full algebra has the same erased shape but a different
annotated tree. This rules out a generic annotation-preserving mirror law.

An explicit local-program separator is stronger. Let R=`n(E,2,leaf3)`.
Direct balR E 1 R gives T with root word[1,2,3]. In contrast,
`mirror (balL (mirror R) 1 E)` first recomputes a root 2 word[3,2,1] on the
left repair, then mirrors without recomputing it. The final erased shape is
the same as T, but the retained root word is [3,2,1], and full cache validity
fails. Hence deriving a raw generic right program by ordinary full-tree mirror
is invalid for this algebra; a separate oriented right proof is warranted.

The intended clients consume actual generic right cache preservation and
unconditional inorder, with fold-fusion or direct combine computation connecting
the stored word to payload inorder. A separate independent height-only proof
would not meet this example's purpose.

### E01: empty payload carrier and separate universes

Instantiate α with an empty type such as PEmpty, σ=Nat×List α, and the ordered
word algebra above. The empty cached tree exists, reads (0,[]), is cache-valid,
and is BalancedD/ValidD for every natural d. Definitions and theorem types for
balL/balR must elaborate without an `Inhabited α` argument. A signature
quantifying a pivot a:α is permitted and then has no concrete pivot inhabitant;
do not fabricate a call `balL E a E` with a nonexistent element. Raw unreachable
branches may reuse a supplied pivot in a generic definition, not choose a global
default. The generic declarations must also remain polymorphic in independent
payload and annotation universes.

### Actual declarations and public laws

Every client name in this table is in the namespace `Examples.HeightRebalance`
and is present in [HeightRebalance.lean](../../Examples/HeightRebalance.lean).
The mapping was authored by `/root/books_remaining` on19 November 2026 against
that client source; independent expectations are attributed above. Public-law
connections include companion declarations and transitive helper use; some
separating calculations use constructive `decide`. Name/source checks here do
not replace the candidate's required type/dependency audit or receiving review.
`AVL` abbreviates `Trees.AVL`; `HB` abbreviates `Trees.HeightBalance`.
Other prefixes are written in full.

| Case | Actual client declarations | Public results consumed |
| --- | --- | --- |
| R01 | `ordinary_empty_left`, `ordinary_empty_right`, `ordinary_empty_valid`, `ordinary_empty_observations` | `AVL.balL_of_ne`, `AVL.balR_of_ne`, `AVL.valid_balL`, `AVL.height_balL_of_ne`, `AVL.height_balR_of_ne`, `AVL.inorder_balL`, `AVL.inorder_balR` |
| R02 | `ordinary_left_strict`, `ordinary_single_heights`, `ordinary_single_validity`, `ordinary_single_inorders` | `AVL.balL_single`, `AVL.valid_balL`, `AVL.inorder_balL` |
| R03 | `ordinary_left_tie`, `ordinary_single_heights`, `ordinary_single_validity`, `ordinary_single_inorders` | `AVL.balL_single`, `AVL.valid_balL`, `AVL.inorder_balL` |
| R04 | `ordinary_double_left_left`, `tagged_left_double_inorders`, `ordinary_double_heights`, `ordinary_double_validity` | `AVL.balL_double`, `AVL.height_balL_double`, `AVL.valid_balL`, `AVL.inorder_balL` |
| R05 | `ordinary_double_left_right`, `tagged_left_double_inorders`, `ordinary_double_heights`, `ordinary_double_validity`, `left_middle_diagram`, `neither_middle_position_is_required` | `AVL.balL_double`, `AVL.height_balL_double`, `AVL.valid_balL`, `AVL.inorder_balL`, `AVL.double_middle_heights_left` |
| R06 | `ordinary_double_left_both`, `tagged_left_double_inorders`, `ordinary_double_heights`, `ordinary_double_validity`, `neither_middle_position_is_required` | `AVL.balL_double`, `AVL.height_balL_double`, `AVL.valid_balL`, `AVL.inorder_balL` |
| R07 | `ordinary_double_right_left`, `ordinary_double_right_right`, `ordinary_double_right_both`, `tagged_right_double_inorders`, `ordinary_double_heights`, `ordinary_double_validity`, `right_middle_diagram` | `AVL.balR_double`, `AVL.height_balR_double`, `AVL.valid_balR`, `AVL.inorder_balR`, `AVL.double_middle_heights_right` |
| R08 | `ordinary_right_strict`, `ordinary_single_heights`, `ordinary_single_validity`, `ordinary_single_inorders` | `AVL.balR_single`, `AVL.valid_balR`, `AVL.inorder_balR` |
| R09 | `ordinary_right_tie`, `ordinary_single_heights`, `ordinary_single_validity`, `ordinary_single_inorders` | `AVL.balR_single`, `AVL.valid_balR`, `AVL.inorder_balR` |
| R10 | `empty_heavy_left_impossible`, `empty_heavy_right_impossible` | `HB.left_ne_nil_of_trigger`, `HB.right_ne_nil_of_trigger` |
| R11 | `empty_middle_impossible` | `HB.ne_nil_of_ht_lt` |
| R12 | `forged_two_branch`, `forged_trigger_separator`, `malformed_inorders` | `AVL.balL_single`, `AVL.inorder_balL` |
| R13 | `forged_three_fallback`, `forged_trigger_separator`, `malformed_inorders` | `AVL.balL_of_ne`, `AVL.inorder_balL` |
| R14 | `raw_cached_tie_branch`, `raw_cached_tie_separator`, `malformed_inorders` | `AVL.balL_single`, `AVL.inorder_balL` |
| R15 | `hidden_actual_trigger_fallback`, `hidden_actual_trigger_separator`, `malformed_inorders` | `AVL.balL_of_ne`, `AVL.inorder_balL` |
| R16 | `correct_root_is_insufficient` | Separating calculation; no generic theorem is asserted by the map. |
| R17 | `retained_bad_descendant_branch`, `retained_bad_descendant_separator`, `malformed_inorders` | `AVL.balL_double`, `AVL.inorder_balL` |
| R18 | `duplicate_unordered_inorder` | `AVL.inorder_balL` |
| R19 | `perfect_valid`, `full_left_range`, `full_right_range`, `full_range_boundary_witnesses`, `lower_boundary_heights` | `HB.node_validD_iff`, `HB.validD_balL`, `HB.validD_balR`, `HB.height_balL_of_ne`, `HB.height_balR_of_ne` |
| R20 | `ordinary_outside_trigger_height`, `outside_trigger_cache_without_balance`, `cache_only_trigger_heights`, `cache_only_trigger_is_not_repair` | `AVL.height_balL_of_ne`, `AVL.height_balR_of_ne`, `AVL.cacheValid_balL`, `AVL.cacheValid_balR`, `AVL.height_balL_single`, `AVL.height_balR_single` |
| R21 | `omitted_lower_bound_fails`, `too_tall_left_node_invalid`, `too_tall_right_node_invalid` | `HB.balL_of_ne`, `HB.balR_of_ne`, `HB.node_validD_iff`, `HB.height_balance_iff` |
| R22 | `single_left_input_valid`, `single_right_input_valid`, `single_outputs_valid`, `single_left_branch`, `single_right_branch`, `single_left_height`, `single_right_height`, `single_child_heights`, `single_heights_two_three` | `HB.balL_single`, `HB.balR_single`, `HB.height_balL_single`, `HB.height_balR_single`, `HB.validD_balL`, `HB.validD_balR`, `AVL.validD_node_actual_iff` |
| R23 | `single_left_height`, `single_right_height`, `single_child_heights`, `single_heights_two_three`, `single_outputs_valid` | `HB.height_balL_single`, `HB.height_balR_single`, `HB.validD_balL`, `HB.validD_balR` |
| R24 | `single_left_height`, `single_right_height`, `single_child_heights`, `single_heights_two_three`, `single_outputs_valid` | `HB.height_balL_single`, `HB.height_balR_single`, `HB.balL_single`, `HB.balR_single`, `HB.validD_balL`, `HB.validD_balR` |
| R25 | `generalized_tie_guards`, `tie_heavy_valid`, `tie_repair_valid`, `forced_double_on_tie_fails` | `AVL.ht_node_smart`, `HB.node_validD_iff`, `HB.validD_balL`, `HB.validD_balR`, `HB.height_balance_iff` |
| R26 | `generalized_left_double_branch`, `generalized_left_double_children`, `generalized_double_positions` | `HB.balL_double`, `AVL.height_node` |
| R27 | `generalized_right_double_branch`, `generalized_right_double_children`, `generalized_right_double_positions`, `right_oriented_double_height`, `right_oriented_double_valid` | `HB.balR_double`, `HB.height_balR_double`, `HB.validD_balR`, `AVL.height_node` |
| R28 | `positive_short_double_height`, `positive_short_double_children`, `positive_short_double_valid` | `HB.height_balL_double`, `HB.balL_double`, `HB.validD_balL` |
| R29 | `middle_balance_is_needed`, `bad_middle_still_has_height_law`, `bad_middle_double_children` | `HB.double_rotation_height_bounds`, `HB.height_balL_double`, `HB.balL_double` |
| R30 | `full_natural_lower_bound`, `truncated_lower_boundary` | `HB.height_lower_bound_iff` |
| R31 | `cast_before_subtraction_matters`, `signed_balance_transport` | `HB.height_balance_iff` |
| R32 | `signed_balance_transport`, `positive_integer_tolerance_transport` | `HB.height_balance_iff`, `HB.int_tolerance_toNat`, `HB.height_balance_int_iff` |
| R33 | `negative_tolerance_separator`, `positive_integer_tolerance_transport` | `HB.int_tolerance_toNat`, `HB.height_balance_int_iff` |
| R34 | `zero_tolerance_branch`, `zero_tolerance_is_not_repair`, `zero_tolerance_inorder` | `HB.balL_single`, `HB.cacheValid_balL`, `HB.inorder_balL`, `HB.validD_nil` |
| R35 | `actual_nontrigger_requires_cache`, `ordinary_outside_trigger_height` | `AVL.balL_single`, `AVL.height_balL_of_ne`, `AVL.height_balR_of_ne` |
| A01 | `maximum_left_branch`, `maximum_right_branch`, `maximum_left_cache`, `maximum_right_cache`, `maximum_both_valid`, `maximum_readers`, `maximum_inorders`, `maximum_fold_fusion`, `maximum_reader_eq_summary`, `maximum_reader_eq_list_maximum`, `maximum_reader_greatest`, `maximum_left_greatest`, `maximum_right_list_maximum`, `maximum_projected_height`, `stale_maximum_height_tests_pass`, `stale_maximum_cache_rejected`, `stale_maximum_full_validity_rejected` | `Trees.MaximumCache.combine`, `HB.balL_single`, `HB.balR_single`, `HB.cacheValid_balL`, `HB.cacheValid_balR`, `HB.validD_balL`, `HB.validD_balR`, `HB.inorder_balL`, `HB.inorder_balR`, `Trees.Cached.read_eq_fold`, `Trees.fold_fusion`, `Trees.MaximumCache.summary_eq_max?_inorder`, `Trees.MaximumCache.summary_eq_some_iff`, `HB.ht_eq_height_of_cacheValid`, `HB.cacheValid_node`, `HB.validD_node_iff` |
| A02 | `word_left_branch`, `word_right_branch`, `word_right_cache`, `word_right_valid`, `word_right_inorder`, `word_right_reader`, `word_fold_fusion`, `word_reader_eq_inorder`, `word_right_semantic_bridge`, `plain_mirror_keeps_the_wrong_word`, `recomputed_mirror_cache`, `recomputed_mirror_observations`, `mirror_derived_right_is_wrong` | `HB.balL_single`, `HB.balR_single`, `HB.cacheValid_balR`, `HB.validD_balR`, `HB.inorder_balR`, `Trees.Cached.read_eq_fold`, `Trees.fold_fusion`, `Trees.Cached.annotate_valid`, `Trees.Cached.erase_annotate` |
| E01 | `empty_payload_word_laws`, `empty_payload_independent_universes`, `empty_heavy_left_impossible`, `empty_heavy_right_impossible`, `empty_middle_impossible` | `HB.cacheValid_nil`, `HB.validD_nil`, `HB.ht_nil`, `HB.left_ne_nil_of_trigger`, `HB.right_ne_nil_of_trigger`, `HB.ne_nil_of_ht_lt` |

## Requirement map and remaining work

| Canonical rows | Formal owners and decisive content |
| --- | --- |
| C09-018–019 | Actual ordinary specializations and exact `balL/R_of_ne`, `_single`, `_double` equations |
| C09-020 | Raw heavy-child and middle-child nonempty laws for every natural tolerance |
| C09-021 | Unconditional erased-payload inorder preservation in both orientations |
| C09-022–024 | Cache-only triggered height alternatives, exact branch effects and fallback height |
| C09-025–026 | Ordinary full recursive validity over the complete one-sided ranges |
| C09-038 | Exact rotation equations, strengthened height diagram, ordinary middle-height disjunction and tagged placement cases |
| C09-054 | Generic shape/cache invariant, complete node characterization, signed arithmetic and positive integer transport |
| C09-056 | Generalized raw programs, all-natural domain/inorder/cache laws and positive-tolerance height/full-repair laws |

This note records mathematical correspondence and complete useful case ownership.
[CTB-118 and current CTB-78 status](../textbooks/CTB.json) distinguish the accepted
donor CONTENT scope from pending receiving validation/review. Old raw development
receipts are historical evidence, not required dependencies of these mathematical
explanations, and are not relabelled as runs of the receiving candidate.

Later donor work now supplies [recursive updates](fdsa-height-updates.md),
[Set refinement](fdsa-height-set-refinement.md) and [fixed-tolerance logarithmic
height](fdsa-height-bound.md). Their existence does not establish the still-open
measured operation costs or C09-060 recurrence/cost specialization. Factor
algorithms, construction 062 onward and later exercises remain in
[the continuation paper](fdsa-avl-continuation.md). Chapter 5's balanced interval,
measured sweep, sharp diameter and encoded polynomial verification, all other
remaining book obligations and current receiving acceptance remain open.
