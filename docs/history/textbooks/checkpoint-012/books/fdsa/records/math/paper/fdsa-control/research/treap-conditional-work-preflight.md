# Treap expected work: conditional-depth and weighted-charging preparation

Recorded 2026-11-02. Bounded mathematical/source preparation for the retained
open C10-117 bridge. Chapter 1 remains the prerequisite and Chapter 10 remains
queued. This is neither a frozen implementation scope nor a proof of accepted
Lean coverage, a final review, or a claim that Theorem 9 has been completely
formalized. The source inventories and earlier reports remain unchanged.

The proposed path was checked absent before use. All file writes were held
until root released checkpoint 0025 capture. Only this report was then written.
There was no implementation, compiler, Lean/Lake, project checker or hash
helper, Git/ref, cache, configuration, gate, enumeration or remote operation.
PDF figures were inspected by rendering them in memory, without writing images.

## 1. Conclusion and exact source boundary

There is a concrete conditional repair route, with three distinct parts:

1. Bound actual per-call work in expectation by a common logarithmic charge
   determined by a coarse pivot-tree frontier. The decomposed treap's whole
   order need not remain uniform: two uniform color restrictions suffice for
   a search-path domination argument.
2. Bound the rank-window cluster size **conditionally on that frontier**.
   Its split-size weight is then fixed, giving the required weighted estimate
   without factoring correlated random variables.
3. Apply the deterministic, ancestor-free layer sum to the resulting root
   charges. This separates actual work from an upper-bound charge and avoids
   asserting that every individual join costs at most its actual split.

Two stronger inferences fail: the recursive minimum-position mean need not
remain at most two after ancestor conditioning, and actual `join2` work need
not be bounded pointwise by its local actual split work. The counterfamilies
below do not refute the advertised **expected total-work** theorem.

Primary source: Blelloch–Ferizovic–Sun, *Joinable Parallel Balanced Binary
Trees*, DOI <https://doi.org/10.1145/3512769>, saved as
`book-source/joinable-2022.pdf` under
`/workspace/scratch/845aa1048b05`. The saved author-PDF URL is
<https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>, CC-BY-4.0;
recorded SHA-256 is
`c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`.
The following pages were read directly:

| Printed page | Relevant source |
| --- | --- |
| 7:4–5 | Work counts primitive operations; after priorities are fixed, the algorithms are deterministic. Equal keys across inputs share priorities. Size is internal-node count and weight is size plus one. |
| 7:8 | Integer layers, rank roots, rank clusters, and ancestor-free sets: Definitions 3–6 and Property 7. |
| 7:17–19 | Treap rank `log₂(weight)−1`, priority-driven pivot join, Lemmas 6–8 and the cluster argument. Figure 10 was inspected visually. |
| 7:19, 7:21–22 | Exact `split`, left-maximum `split_last`/`join2`, and the three bulk operations. Figures 11 and 13 were inspected visually. |
| 7:24–28 | Theorem 9, Table 3, Theorem 10's join comparison, Theorem 11's layer analysis and the weighted-cluster display. The latter display was also inspected visually. |

Retained context: `chapter10-obligations.md` C10-112–118;
`probability-source-preflight.md` §3.3;
`permutation-expectation-source-preflight.md` §§4 and 6; and the earlier
relative-order/tail/joint-law preflights. The contemporaneous
`permutation-placement-order-preflight.md` treats fixed-set position/internal-
order independence. Its fixed-global-law result is useful but does not resolve
the adaptive-descendant counterfamily here.

## 2. Fixed inputs, one ranking, and the actual cost being analyzed

Use **A for the pivot input** and **B for the decomposed input**. Thus the
paper's Figure 13 call is `op(T_B,T_A)`, and its directional difference is
`B \ A`. The sets A and B are fixed finite subsets of a total key order before
sampling. Sample one uniform distinct priority ranking of `A ∪ B` and restrict
it to both canonical treaps. Earlier/smaller priority means nearer the root.
Shared keys are one sample label with one priority, not independent copies.

Write `a=|A|`, `b=|B|`, `m=min(a,b)`, `n=max(a,b)`. Preserve the C10-117 target
with `1≤m≤n`, fixed input-independent constants, and the actual constant-work
empty-operand base cases. The target is expected primitive work, not a
pointwise balance theorem or a high-probability work theorem. Building the
random input trees is not silently added to or removed from an operation's
declared tariff. Root/child access, comparisons and local constructors need
explicit bounded costs in the eventual implementation.

The exact helper matters. Figure 11's `join2(L,R)`:

- returns R immediately when L is empty;
- otherwise extracts the **maximum from L** by following its right spine;
- reconstructs that path with the same pivot join;
- calls `join(L_without_max, max_L, R)`.

It has no separate right-empty shortcut. This is not a specialized two-treap
merge. The book's Chapter 10 helper instead uses right-minimum extraction,
with a right-empty base case. C10-114 still requires the corresponding
algorithm/work bridge; equality of result sets or canonical output trees is
insufficient for equal execution costs. Likewise, preserve the paper's pivot
operand convention when relating its recursion to the book's routines.

## 3. What the printed probabilistic steps do not establish

### 3.1 Unconditional cluster expectation does not justify weighted extraction

On p.7:28, the display moves the varying `d(v_kj)` outside a double sum and
does not expose an expectation or conditioning operation. It is not a valid
literal algebraic identity. Even after inserting expectations,
`E[d]≤C` alone does not imply `E[d Z]≤C E[Z]` for the correlated split-size
weight Z. Random rank-root membership also needs an indicator or a fixed
indexing set. The appropriate replacement is the conditional inequality in
§7, not an assertion of unconditional independence.

### 3.2 Fixed-subset minimum position is insufficient at a recursive call

For fixed nonempty S under the original global uniform law, the first
position mean is `(U+1)/(|S|+1)`. The fixed-S position/internal-order
independence route is also valid. Neither statement says that this placement
law survives an ancestor-reveal event for a descendant set.

Here is an exact family using fixed inputs and the same original ranking.
Let A consist of k lower keys followed by a higher set S of size t. Let B
consist of s disjoint keys above all those lower keys, inside the remaining
key interval. Condition the A-relative order to put its k lower keys first,
in increasing key order. The pivot recursion follows k right children and
then reaches the subproblem `(S,B)`; B has not lost any key.

Given this event, the root of S is the `(k+1)`-st key in A's priority order.
For each fixed key of B, its insertion slot among the `k+t` A keys is uniform
over `k+t+1` slots. The event constrains only A's internal order, so this
single-key slot calculation is unaffected. Linearity, without independence
among B slots, gives the one-based position among `S ∪ B`:

```text
E[local position of min(S) | ancestor event]
  = 1 + s*(k+1)/(k+t+1).
```

For t=s this tends to `s+1` as k grows. The stricter source branch is reached
by taking **t=2s and k=4s²**: then `|S|>|B|`, yet the mean is at least
`1+(2/3)s`. For example s=2 gives `55/21>2`. The inequality follows from
`3(4s²+1)−2(4s²+2s+1)=(2s−1)²≥0`.

These are positive-probability conditioning events. The initial sets are not
chosen after sampling. This refutes transporting the paper's at-most-two
root-position estimate to every recursive ancestor-conditioned subproblem.
It does not contradict the unconditional fixed-S law or Theorem 9: the
conditioning event itself can be rare. Nor does it refute conditional
uniformity of the **internal remaining order** on S, which still holds.

For a genuinely fixed top-level A and B, pivot-join recursion depth is at
most the number of keys before A's minimum, plus one. The fixed-set mean
therefore supplies a constant bound directly when `|A|≥|B|`, without Jensen.
That simpler fact must retain its fixed-global-law premise.

### 3.3 Actual local join2 work can exceed actual local split work

For h≥1, use ordered keys

```text
L={1,…,h} < b < a < c < r,
A=L ∪ {a,r},                 B=L ∪ {b,c,r}.
```

Assign priority order `b,c,a,1,2,…,h,r`. The A treap has root a, left subtree
the h-node right chain L, and right singleton r. The B treap has root b,
left subtree L, and right root c with empty left child and right singleton r.
Splitting B at a visits only b and c. Its reconstruction joins are immediate
because their original pivots still have priority above every retained child.
This local split has bounded primitive work independently of h.

Intersection's two recursive results are L and `{r}`. Since a is absent from
B, its final operation is the actual Figure 11 `join2(L,{r})`. Extracting
max L visits h nodes, and the final pivot join traverses the L boundary again.
Thus this local join2 work grows with h. The complete recursive intersection
also does other work; that work is not omitted from the eventual total bound.

There is an expected version of the same boundary: condition only that the
first three global priority labels are `b,c,a`. The remaining order on
`L ∪ {r}` is uniform, while the split still visits exactly b and c. The
expected right-spine extraction length is `H_h`, so expected join2 work is
at least a positive constant times `H_h`. Consequently a pointwise or
arbitrary-history interpretation of “join work no more than actual split
work” cannot be used here.

The sufficient replacement is that joins and splits have the **same
conditional logarithmic upper charge**, as established by the route below.
This does not purport to certify every literal reading of Theorem 10.

## 4. The precise coarse history that leaves usable laws

Index the full canonical A treap mathematically, even below branches the
operation will prune. For a fixed binary address, reveal only the root-key
identities at its proper A ancestors. A feasible positive-probability history
atom H determines:

- the open key interval I specified by those ancestor comparisons;
- the remaining pivot set `K=A∩I` and its size/weight `W=|K|+1`;
- the parent's size and integer rank layer, hence rank-root eligibility;
- the decomposed set `B_I=B∩I`, its cardinality q, and
  `Z=log₂(q+1)`.

Within each fixed atom, the relative priority order on K is uniform. Prove
this by induction over the specified ancestor minima: the conditional tail
law removes the exposed root, then the fixed-subset restriction law selects
the indicated child interval. The child subset is fixed on that atom. There
is no theorem about an arbitrary adaptive subset under the original measure.

If a present node has q>0, all its ancestors also have positive decomposed
size, so the actual bulk recursion reaches it. If q=0, that branch terminates
at a base case. This call/interval relation must be proved for Figure 13;
it depends on set-valued split correctness, not on B's priority order.

Condition further on the current A root being a particular key v when
analyzing its operation. The remaining K order is uniform on `K\{v}`.
For `D=(B\A)∩I`, relative uniformity follows differently: the original fixed
sets A and `B\A` are disjoint, so their complete relative orders are
independent under the one global ranking. H and the current-root event are
events determined by the A order. They therefore leave D's relative order
uniform, followed by restriction to the now-fixed I.

Do not condition on the complete A tree, all its internal priority order, or
the full split execution and then assert the same K law. In particular B
priority tests may reveal information absent from H. The analysis is allowed
to use a coarser sigma-field than the execution observes; the tower/finite
partition identity still applies to actual work. It must not describe that
coarse law as the law conditional on all execution information.

All statements here can be expressed on finitely many positive-probability
history atoms using ordinary conditional measures. Null atoms contribute
zero to the unconditional sum and need no fictitious normalized law.

## 5. A sufficient conditional split-depth domination

After fixing H and root v, partition the actual decomposed keys as

```text
C = (A∩B∩I) \ {v},        D = (B\A)∩I,
B_I = C ∪ D ∪ ({v} if v∈B else ∅).
```

C is a fixed subset of the remaining uniform K order. D is a fixed subset
of the B-only order independent of the A history. Thus **each** has a uniform
relative order. Their merged interleaving may be biased and no independence
between the two search lengths is needed. If v belongs to B, it is the
minimum-priority shared key; the entire shared group including v is not
uniform after the root conditioning. Keep the exceptional singleton separate.

Use the deterministic Cartesian-treap search criterion: a key x is visited
when searching for v exactly when x has the earliest priority among the
tree keys in the closed key interval between x and v, with the appropriate
present/absent query interpretation. Therefore, if x is visited in the union
treap, it is also visited in its own color-restricted treap: minimizing over
the larger interval set implies minimizing over its color subset. Pointwise,

```text
searchVisits(B_I,v) ≤ 1 + searchVisits(C,v) + searchVisits(D,v).
```

The extra one permits the actual key v. In both color searches v is absent.
For a fixed absent query with ell keys to its left in a uniform treap on q'
keys, the interval-minimum indicators give exact expected visits
`H_ell + H_(q'−ell) ≤ 2H_q'`. Set `H_0=0`. Thus the conditional combined
mean is at most `1+4H_q`, and is `O(log₂(q+1))` for active q≥1. No expected
global height theorem or fresh uniform law on the combined B_I is required.

The actual split reconstruction also needs its pointwise bridge. In
Figure 11 each reconstructed join uses an original B node as its pivot;
all its retained children are restrictions of that node's original children.
That pivot still has earliest priority, so Figure 10 returns its node without
recursive join descent. Each search visit therefore causes only bounded
additional reconstruction work. This supplies the primitive-work version of
the search bound, once proved against the chosen explicit empty-node cases.

## 6. Join and join2 under the same logarithmic charge

### Union: direct pointwise domination is available

The final union contains K and B_I, including current pivot v. Since v is
the earliest-priority key of K, every strict ancestor of v in that canonical
union treap belongs to `B_I\K`. Such an ancestor minimizes priority on the
union's key interval to v, hence also on B_I's interval to v. It is therefore
visited by the same local split search in B_I.

Figure 10 pushes v down one level per recursive join call, so its join work
is bounded by a fixed constant times `1+searchVisits(B_I,v)`. This uses actual
tree/search relations and shared priorities; it does not use the false
recursive at-most-two placement estimate. The required pointwise canonical
treap and recursion/value lemmas are still to be implemented.

### Intersection and difference: use the actual boundary extraction

For intersection, if v∈B, the final pivot v has earliest priority in the
entire result, a subset of K, so its join is immediate. If v∉B, the result
key set `R=K∩B_I` is a fixed subset of `K\{v}` under the current conditioning;
its relative order is uniform. For difference, the result is
`R=B_I\K=(B\A)∩I`, whose order remains uniform by the B-only argument.
These laws concern the **actual recursive results**, via canonical treap
uniqueness and the operations' pointwise set/heap correctness.

The left and right returned sets are the fixed parts of R below and above
v. When the left part is nonempty, let p be its maximum key. Figure 11's
work can be bounded pointwise by a constant times

```text
1 + rightSpineLength(T_(R_left)) + depth_(T_R)(p).
```

The extraction reconstruction joins are immediate for the same reason as
split's reconstruction. Its final pivot join pushes p down to its actual
depth in the canonical result T_R. Here p is determined by the fixed key
set, not by a fresh priority minimum. Under a uniform relative order,
expected right-spine length is `H_|R_left|`, and a fixed key with ell keys
below and r keys above has expected depth
`H_(ell+1)+H_(r+1)−2`. Both are logarithmically bounded in `q+1`, since
`|R|≤q`. If the left result is empty, Figure 11 returns the right result in
constant work. The right-empty case still includes the extraction cost.

This gives a conditional common logarithmic charge for all three operations.
It makes no independence claim about recursive costs, and it does not assert
that this join2 cost is bounded by the actual local split cost. Linearity and
finite conditioning suffice for expected work.

## 7. Repair the weighted rank-cluster step with a finite induction

For the paper's nonempty treap rank `r(T)=log₂(w(T))−1`, the descendants in
the relative window `(r(v)−1,r(v)]` have weight **strictly greater than W/2**,
where W is the root weight. There can be at most one qualifying child:
child weights sum to the parent weight, which is at most W. The window is
therefore a chain. Use `2*childWeight>W` for an exact natural-number test.

Given only the proper-ancestor history H, K has uniform internal order.
For a current nonempty subtree of weight x, the root is uniform among its
`x−1` keys, so its two child weights are j and `x−j`, with j uniform over
`1,…,x−1`. Direct finite sums give

```text
E[max(j,x−j)] ≤ 3*x/4.
```

For x=2u, the exact mean is `(3u²−2u)/(2u−1)`; for x=2u+1 it is
`(3u+1)/2`. The smallest active weight is two. No approximation, independently
repeated shrinkage, or unproved geometric survival formula is used.

The economical proof of the constant is finite strong induction on current
key count, with original W fixed. Let L_W be the length of the heavy-child
chain until weight is at most W/2. Claim, for uniform current order and
`1≤x≤W`,

```text
E[L_W at current weight x] ≤ 8*x/W.
```

The inactive case has length zero. In the active case, expose the root;
the chosen child's order is uniform conditionally, its key count strictly
decreases, and the induction hypothesis applies. Hence

```text
E[L_W] ≤ 1 + 8*E[largest child weight]/W
       ≤ 1 + 6*x/W
       ≤ 8*x/W,                         because x>W/2.
```

At x=W this gives `E[d | H]≤8`. One may instead use the existing accumulated-
work/drift formulation with absorption; no infinite-process construction is
required by this proof. If indexing by a fixed key v rather than an address,
also condition on v being the current root. Charge that forced first node
separately; the chosen descendant subtree still has a uniform conditional
order. The safe bound is then **9**. This finite-key formulation avoids a
new address-indexing abstraction and is the preferred economical future
implementation route: for each fixed v∈A, the ancestor-plus-current-key
history events partition its sample space. The first cluster step alone is
already exposed, and `1+8*x_child/W≤9` handles it. The sharper constant eight
is unnecessary for the retained uniform Big-O target.

Root eligibility and `Z=log₂(1+q)` are already fixed by the appropriate
history. For fixed-key indexing, the valid replacement for the paper's
extraction is therefore

```text
E[1_rankroot(v) * d(v) * Z(v)]
  ≤ 9 * E[1_rankroot(v) * Z(v)].
```

Sum over the fixed finite set A. This explicitly handles the random set of
rank roots. It does not require d and Z to be independent.

### Coverage and rank-rounding qualifications

The relative rank windows in Definition 5 need not be disjoint across
different integer layers. For a safe charging partition, assign each node
to its highest ancestor in the **same integer layer**. These components
partition the nodes and are contained in the corresponding relative-window
clusters. Descendant intervals are subsets of the root interval, so Z never
increases along that component. Thus, pointwise,

```text
sum_nodes Z ≤ sum_rankroots d(v)*Z(v).
```

No equality of overlapping window clusters is claimed. With the stated
rank, integer layer k corresponds to weights in
`[2^(k+1),2^(k+2))`, whereas the printed Lemma 7 calculation uses
`[2^k,2^(k+1))`. Its approximate probability and its cluster-size/grandchild
wording should not be imported as exact finite identities. The threshold
and contraction calculation above avoid those indexing ambiguities.

## 8. Where the remaining layer sum fits

For a fixed realized pivot tree, rank roots of a fixed nonnegative integer
layer k are ancestor-free. Their A-subtrees and their B intervals are
disjoint. If s_k counts only roots with q>0, then

```text
sum_at_layer q_v ≤ b,
s_k ≤ b,
s_k ≤ a / 2^k.
```

The last sufficient bound follows because a layer-k root has at least
`2^(k+1)−1 ≥ 2^k` internal nodes. This uses the actual size/weight conversion,
not the paper's loosely shifted logarithm notation. Concavity then gives
`sum_at_layer log₂(q_v+1) ≤ s_k*log₂(1+b/s_k)` for positive s_k; a zero
layer contributes zero.

The resulting geometric layer sum has a direct elementary bound by a
constant times `m*log₂(1+n/m)`: for a≤b, substitute `a/2^k` and use
`log₂(1+2^k b/a) ≤ k+log₂(1+b/a)`. For a>b, use `s_k≤b` below
`ceil(log₂(a/b))`, then the geometric bound above it. Finite sums can be
bounded by the usual sums of `2^(−k)` and `k*2^(−k)`. This part is pointwise
and does not factor random cluster lengths out of a random sum.

The logical order is important. First, the conditional work estimates in
§§5–6 give an expected-work bound by `E[sum_nodes Z]`. Next use the pointwise
component domination, then the conditional cluster inequality, and finally
the pointwise root-layer sum. Do not first assert a pointwise logarithmic
work bound for every treap.

Base-case/control work also needs its explicit small bridge. The pruned
binary recursion has at most a constant times its number of active calls
plus one total calls. Each active q≥1 has `Z≥1`; q=0 immediately terminates.
Thus base and between-helper work can be absorbed into the same charge plus
a fixed additive constant. Empty original operands are handled directly.

## 9. Named remaining lemmas and handoff

This is a checkable proof route, not a declaration that the whole theorem is
proved. The future Lean work still has to establish these exact connections:

| Required lemma / bridge | Why it cannot be skipped |
| --- | --- |
| Canonical treap uniqueness and interval-minimum ancestor/search characterization | Connects actual tree paths, union ancestors and color-restricted search paths to priority events. |
| Figure 13 call/interval correspondence | Makes K, B_I, pruning and active-call accounting refer to actual recursion, with directional difference preserved. |
| Coarse ancestor-history uniform law, including current-root conditioning | Supplies the precise remaining-order law for adaptive descendants on each fixed history atom. A global fixed-subset theorem alone is insufficient. |
| B-only internal-order conditioning and fixed-subset restriction | Uses disjoint A/B-only relative-order independence; it does not assert a uniform shared/B-only interleaving. |
| Harmonic search, fixed-key depth and boundary-spine means | Supplies the conditional bounds used for split and actual left-maximum join2. Each is over fixed keys under the appropriate conditional relative-order law. |
| Pointwise primitive-work recurrences and erasure for join, split and split_last/join2 | Establishes immediate reconstruction joins and the actual path-based work bounds under a declared tariff, including empty-node handling. |
| Same-layer component coverage and conditional cluster-length induction | Repairs both random root membership and the unjustified weighted extraction. |
| Layer sum, finite expectation assembly and base-call charge | Produces uniform constants and the stated min/max size dependence, retaining zero cases. |
| Book-versus-paper execution/work correspondence | The helper extraction side and pivot operand differ in places. Canonical output equality is not an exact cost bridge. |

The existing probability observations, ordinary conditional measures, fixed-
subset restriction/tail laws and disjoint-order law are the appropriate
infrastructure. They remain subject to their own validation status. No new
priority sampler, tree executor, conditional-probability framework, or frozen
shared abstraction is proposed by this note.

A bounded read-only child analysis independently supplied the frontier/
cluster argument, exact finite child-weight sums, coverage distinction and
two-color search domination; it wrote no file and ran no compiler or
enumeration. Root separately inspected the source figures and the join2
counterfamily and suggested the economical finite induction used here.
These checks improve the mathematical handoff but are not the project's
independent final review or chapter acceptance. C10-117 and all related
algorithm, cost and correspondence obligations remain open.
