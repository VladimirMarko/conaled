# Chapter 27: primary-source recovery for the lattice graph/cache extension

Research date: 2026-11-02. Parent inventory: **chapter27-obligations.md**,
obligations **C27-180–185**, with links from C27-067 and C27-179.

**State: queued source preparation.** This note recovers the particular
construction needed for the mathematical assertion on FDSA printed p.340.
It is an original mathematical handoff, not a Lean implementation, checked
proof, chapter acceptance, or an expansion to the entire cited paper.
The existing inventory was preserved before this recovery clarification.

## 1. Source identity, content pins and access limit

The cited construction is **Alpha-beta duo**, Algorithm 2 in Junkang Li,
Bruno Zanuttini, Tristan Cazenave and Véronique Ventos, *Generalisation of
Alpha-Beta Search for AND-OR Graphs With Partially Ordered Values*,
IJCAI 2022, pp.4769–4775, DOI
[10.24963/ijcai.2022/661](https://doi.org/10.24963/ijcai.2022/661).
The official [proceedings record][I-record] and [published PDF][I] establish
the identity. The bounded recovery uses its graph/value definitions,
Algorithm 2, Definitions 4–5, Propositions 2–3 and Corollary 2.

The short paper points to **hal-03656224** for full proofs. The primary
[HAL API][H-api] identifies the current report as **hal-03656224v2**,
document ID **3676696**: report date 2022-05-02, submission
2022-05-24 11:07:06 UTC, release 2022-06-10 11:09:04 UTC.
Its 2026-02-07 metadata modification is not evidence of a new manuscript
revision. The [versioned PDF request][H-v2] returned **HTTP 403**.
No HAL PDF was read or hashed, and no access restriction was bypassed.

An accessible primary long version is in the official
[JIAF/PFIA 2022 proceedings][J], printed and physical PDF pp.101–111.
The article's first-page footnote identifies it as the long version with
full proofs of the IJCAI paper. The JIAF author order is Li, Zanuttini,
Ventos, Cazenave. The short and long publications were read independently;
the JIAF article is **not claimed to be identical to inaccessible HAL v2**.
The complete proofs needed here are present in JIAF pp.106–108.

### Reading-input pins

All paths in this table are relative to the workspace's **book-source/**
directory. These downloaded reading sources are distinct from this
original deliverable. URLs without a content version are pinned here by
their retrieved bytes, not described as permanently immutable.

| Reading input | Bytes | SHA-256 |
|---|---:|---|
| Li-Zanuttini-Cazenave-Ventos-2022-ijcai-0661.pdf | 428,891 | 40b74489ad38e56e0893eeef1818a692d40eb5f4aef0a985324c616436b8c8d5 |
| Li-2022-HAL-api-full.json | 79,461 | f8114bcb910507193dc236f1899d79c121004df86525fc8921fb02eb1791b249 |
| Li-2022-HAL-alternative-JIAF-proceedings.pdf | 6,746,419 | 18642d76394aea5264da7194d57f2ced0da8577fcd57bd5fd044493be839fa3a |
| Li-2022-HAL-alternative-JIAF-article.pdf | 620,265 | 2be7c3f0971be768fd40f9b8332d53eff3a013451003a74611b0ca34ad15c92e |
| Li-2022-HAL-alternative-JIAF-article.txt | 82,801 | f53231db6abc56421b95baa4aa6becd37e9dae18e3e3e91e3bc65254cae03a67 |
| Li-2022-HAL-recovery.provenance.json | See the file | 8c77bbd78dd6a798c5cc85be232e305009b2be43a393108c766ddbc773c5ecbe |

The 11-page article PDF is a reading extraction from the 147-page
proceedings, not a standalone download from HAL. The provenance JSON
records the extraction, API fields, HTTP access failure and file hashes.
The official short PDF reports creation/modification on 2022-07-18;
its downloaded HTTP Last-Modified is 2022-07-18 15:21:55 GMT.

The initiating book is the July 27, 2026 PDF at
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>,
SHA-256 **9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645**.
The Chapter 27 inventory separately pins its AFP tree development; that
formal source does not supply this graph/cache implementation.

### Rights and implementation-source evidence

The HAL metadata records **HAL authorisation v1**, not a Creative Commons
or software license. The [HAL explanation][H-rights] retains author rights
and distinguishes reading and attributed quotation from broader reuse;
its webpage footer license does not license the deposited article.
HAL also explains that this metadata label can be assigned to older
deposits lacking another recorded license. The [IJCAI publisher policy][I-rights]
permits publication of paper versions with a visible reference and link
to IJCAI Organization; this is a specific publication permission, not an
identified code license.

No source-code repository, code attachment, or software license was
identified in the inspected official short paper, long article, or HAL
file list. No article-specific open adaptation license was found in the
JIAF article. This handoff restates mathematics and records source
locations; it does not redistribute a paper or copy an implementation.

Separate records hal-03658915 and hal-03658925 are not established aliases
for the footnoted report. An apparent arXiv association, 2109.05799, was
rejected because it identifies a different Neumann–Witt paper.

### Exact source-to-obligation map

| Material needed for the book assertion | IJCAI location | JIAF long location | Inventory |
|---|---|---|---|
| Bounded distributive lattice; rooted AND-OR graph; value recurrence | §§2–3, p.4770 | §§2–3, p.102 | C27-181 |
| Why a single lattice-valued return is not a safe ordered cache flag | §5, p.4772; Fig.1, p.4770 | §5, pp.105–106; Fig.1, p.103 | C27-182–183 |
| Window-independent lower/upper initialization | Definition 4, p.4772 | Definition 4, p.105 | C27-182–183 |
| Actual cached recurrence | Algorithm 2, p.4772 | Algorithm 2, p.106 | C27-182 |
| Cache coherence, including exact leaves | Definition 5, p.4772 | Definition 5, p.106 | C27-183–184 |
| True-value bracketing and refinement | Proposition 2, p.4773 | Proposition 2, pp.106–107 | C27-183–184 |
| Equal squashes of the returned endpoints | Proposition 3, p.4773 | Proposition 3, pp.107–108 | C27-183 |
| Enclosing-window recovery and full-window exactness | Corollary 2, p.4773 | Corollary 2, p.108 | C27-183–185 |

The experimental optimization following Corollary 2 and the benchmark
campaign are not needed to witness the particular book assertion. This
bounded recovery does not silently substitute the optimized program for
Algorithm 2 or create an obligation to reproduce the entire paper.

## 2. Graph, value and progress domain

Use a fixed rooted graph \(G=(N,C,r,\operatorname{kind})\).
Each node has an AND or OR label. The source explicitly permits
consecutive nodes of the same label. Every node is reachable from the
root, and the root has no predecessor. Children form a set \(C(n)\);
the executable algorithm uses an enumeration of that set.

The formal executable domain must make finiteness/progress explicit:
use a **finite acyclic graph**, with a finite, complete, duplicate-free
ordered child enumeration at each node. A child rank into natural numbers,
strictly decreasing along every edge, is a convenient termination
witness. An equivalent generalization may use a well-founded child
relation and finitely enumerable children, but must not drop either
condition. Reachability and the distinguished root express the paper's
domain; the correctness theorem applies to calls at any node.

The value carrier is an arbitrary **bounded distributive lattice**,
not necessarily finite or totally ordered. Concrete execution additionally
needs executable lattice operations, the cutoff comparison and the
equal-bound decision; a mathematically defined comparison on arbitrary
reals is not automatically an executable implementation.

A leaf is exactly a node with no children. Fix an evaluation \(e\) on
those leaves. Define the true value independently of the cache:

\[
v(n)=
\begin{cases}
e(n), & C(n)=\varnothing,\\
\bigvee_{c\in C(n)}v(c), & C(n)\ne\varnothing,\ \operatorname{kind}(n)=OR,\\
\bigwedge_{c\in C(n)}v(c), & C(n)\ne\varnothing,\ \operatorname{kind}(n)=AND.
\end{cases}
\]

The joins and meets are finite. Prove well-definedness/uniqueness and
invariance under another complete child enumeration. Value invariance
does not assert equality of pruning traces, returned intervals, or cache
states for different orders.

### D27C-1: the source's acyclicity premise needs a finite-computation qualification

Both primary versions allow an unspecified node set and justify the
recursive value merely by calling the graph acyclic (IJCAI p.4770;
JIAF p.102). They subsequently enumerate \(n_1,\ldots,n_b\) and perform
structural induction. A finite graph is the intended computational
setting, but acyclicity alone on an unrestricted set is insufficient.

An independent counterexample to the literal unrestricted reading is
\(N=\mathbb N\), root 0, \(C(n)=\{n+1\}\), with every node OR. This is
rooted and acyclic, but it has no leaf and an infinite path. In the
Boolean lattice, both constant-false and constant-true functions satisfy
the putative value equations. Empty leaf data therefore does not
determine a unique value. Algorithm 2 with the default internal interval
and the full window recurses indefinitely.

Retain this as a future checked counterexample and prove the corrected
finite-DAG theorem. Calling the edge relation well-founded without
requiring finite child enumeration would still be inadequate: the loop
must terminate and a merely bounded lattice need not have infinite
joins/meets. This is an explicit source-domain qualification, not a
claim that the authors intended an algorithm for infinite games.

### Keys identify this fixed value problem

Source cache keys are **node identities**; entries are pairs of values.
Neither the window nor a depth is part of the key. The source graph has
no bounded-depth parameter, cyclic-game solution rule, symmetry quotient,
hash-collision policy, eviction policy or concurrent mutation.

A depth-limited game adapter must make its state identify the relevant
value problem, for example by using position/depth pairs in an acyclic
expanded graph. Reusing a key after changing the evaluator, graph,
remaining depth or a symmetry representative needs a proved
value-preserving correspondence. Those adaptations are not implicit
properties of the cited algorithm.

## 3. Initialization and cache contract

Let \(h_L,h_U:N\to V\) be fixed, window-independent functions. The source
admissibility condition is:

\[
h_L(n)\le v(n)\le h_U(n),
\qquad
C(n)=\varnothing\Longrightarrow h_L(n)=h_U(n)=v(n).
\]

The default pair is \((\bot,\top)\) at internal nodes and
\((e(n),e(n))\) at leaves. These functions need not be exact internally.
The theorem does not give their evaluation cost for free.

Represent the finite cache extensionally as
\(\sigma:N\to\operatorname{Option}(V\times V)\), realized through an
appropriate existing map interface. **Coherence** means:

\[
\sigma(n)=\operatorname{some}(l,u)
\Longrightarrow
l\le v(n)\le u,
\]
\[
C(n)=\varnothing\ \land\
\sigma(n)=\operatorname{some}(l,u)
\Longrightarrow l=u=v(n).
\]

The empty cache is coherent. A hit uses its stored interval as-is;
the algorithm does not additionally intersect it with the heuristic
interval. Source initialization is therefore independent of windows,
whereas the preceding uncached Algorithm 1 has a different heuristic
contract. Do not interchange the two contracts.

### B27C-1: leaf exactness is essential

The code has no independent leaf branch. Consider a single Boolean OR
leaf with value true, full window, and a cached interval (false,true).
It brackets the true value, but it fails the source's extra leaf
condition. The unequal-bound guard proceeds to an empty child loop;
the OR accumulators remain (false,false), so the returned upper bound
is false. This violates bracketing.

This is a boundary witness for why Definition 5 includes exact leaf
entries, not a counterexample to the source theorem. Retain the positive
exact-leaf execution and this weakened-premise counterexample in future
checked examples.

### B27C-2: cache state is a semantic input

In the chain \(0<1<2\), take an OR root with one leaf of value 2 and call
with window \((0,1)\), using default initialization. A coherent cached
root interval \((1,2)\) yields a cutoff before the child and returns
\((1,2)\). Starting with an empty cache visits the child and returns
\((2,2)\). The graph, node and window are identical.

Thus the paper's abbreviated notation \(f(n,a,b)\) suppresses state;
the future formal definition must expose the initial and final cache.
All theorems quantify over coherent initial states. Raw returned
intervals need not be independent of the initial cache.

## 4. Exact stateful recurrence

Write
\[
\operatorname{duo}(n,a,b,\sigma)=((l,u),\sigma').
\]
The following equations restate Algorithm 2 with explicit state. They
are a specification of the actual computation to implement later,
not an extensional replacement that first computes \(v(n)\).

1. Read \((c_L,c_U)\) from the entry for \(n\), or use
   \((h_L(n),h_U(n))\) on a miss.
2. If \(c_L=c_U\), return \(((c_L,c_U),\sigma)\) immediately.
   This branch includes exact internal nodes as well as leaves.
3. Initialize \(A=a\vee c_L\) and \(B=b\wedge c_U\).
   For OR, initialize \(L=U=\bot\). For AND, initialize \(L=U=\top\).
4. Process the selected child list from left to right, carrying
   \((A,B,L,U,\sigma)\). With no children remaining, finish the loop
   without another cutoff test. With a remaining head child \(q\):
   - If \(B\le A\), end the loop immediately, replacing \(U\) by \(c_U\)
     at OR nodes, or replacing \(L\) by \(c_L\) at AND nodes.
   - Otherwise run \(\operatorname{duo}(q,A,B,\sigma)\).
     If it returns \(((l_q,u_q),\tau)\), the next loop state at OR is
     \((A\vee l_q,B,L\vee l_q,U\vee u_q,\tau)\).
     At AND it is
     \((A,B\wedge u_q,L\wedge l_q,U\wedge u_q,\tau)\).
5. At loop completion set \(l=L\vee c_L\) and \(u=U\wedge c_U\).
   Overwrite the cache entry at \(n\) with \((l,u)\), then return
   that pair and the updated state.

The stored initial endpoints \(c_L,c_U\) are read once per activation.
Recursive child calls use the latest cache returned by preceding calls.
Termination follows from the graph progress witness for child recursion
and finite list descent for the local loop.

### Operational details that a correspondence theorem must retain

| Detail | Consequence |
|---|---|
| Exact hit or exact heuristic returns before traversal | On an exact miss, even at a leaf, no new entry is inserted. “Every visited node is cached” is false for the printed algorithm. |
| Cutoff is checked before the next child | A cut before child 1 is allowed. There is no additional restoration after the last child has already finished. |
| OR initializes both accumulators to bottom; AND both to top | The accumulator pair is not initialized to (bottom,top). |
| OR updates the window with the child lower endpoint; AND with the upper endpoint | Updating with the other endpoint is a different algorithm. |
| At a cut, OR restores its old upper bound; AND restores its old lower bound | The unvisited children make the corresponding partial accumulator an invalid whole-node bound. |
| Final intersection uses the entry-time interval | The returned interval refines the prior knowledge; it is then stored by overwrite. |
| Child enumeration is observable to execution | Set equality of children justifies value equality, not identical work or cache behavior. |
| Repeated graph positions use the same key | Finite unfolding duplicates occurrences semantically, while cache reuse shares bounds operationally. |

The finite-DAG premise prevents the current node from recurring below
itself. It does not prevent a later branch from reaching a node visited
in an earlier branch. The cache is not a “visited once” set: an inexact
entry can be revisited under another window and refined again.

## 5. Complete correctness relation

Fix the corrected graph domain, the bounded distributive lattice,
admissible initialization and a coherent initial cache. Let an actual
terminating call return \(((l,u),\sigma')\).

### Value and state facts: Proposition 2

The returned interval brackets the true value:
\[
l\le v(n)\le u.
\]

If an entry \((c_L,c_U)\) existed for \(n\) before the call, then:
\[
c_L\le l,\qquad u\le c_U.
\]

The final cache is coherent. More explicitly, the state theorem should
retain the prose assertion that stored intervals never become looser:
every previously present entry remains present, with its lower endpoint
nondecreasing and its upper endpoint nonincreasing. Untouched keys keep
their entries. This follows from child-state induction and the final
store; it is not obtained merely by proving the returned pair correct.
The exact-pair branch leaves the whole cache unchanged.

### Equal squashes: Proposition 3

Define the paper's squash operation
\[
S_{a,b}(x)=b\wedge(a\vee x).
\]
For **all** \(a,b\), including incomparable or reversed windows:
\[
S_{a,b}(l)=S_{a,b}(u).
\]

Together with the bracketing result and monotonicity, this gives the
complete observation relation:
\[
S_{a,b}(l)=S_{a,b}(v(n))=S_{a,b}(u).
\]

There is no premise \(a\le b\), and no total-order trichotomy is used.
The public contract is a pair of unconditional global bounds plus this
window observation and the state invariant. A correctness statement for
one scalar return with no cache parameter loses required information.

### Recovery of the exact value: Corollary 2

If \(p\le v(n)\le q\) and the call uses window \((p,q)\), then
\[
v(n)=S_{p,q}(l)=S_{p,q}(u).
\]
In particular, a full-window call satisfies
\[
a=\bot,\ b=\top\Longrightarrow l=u=v(n).
\]

For an arbitrary enclosing window, the endpoints themselves need not
coincide. Example: in \(0<1<2\), an OR root with ordered leaf values
\([1,0]\), empty cache and window \((0,1)\) returns \((1,2)\);
the cutoff before the second leaf restores the old upper bound 2.
Both endpoints squash to the true value 1.

Since cached endpoints bracket the true value without reference to the
old window, the final coherent cache can be reused in later calls with
different windows. This claim keeps the same graph/evaluator/key
semantics; it does not license an unrelated value problem.

### Bridge to the book's squash convention

The book uses \(C_{a,b}(x)=a\vee(x\wedge b)\). Distributivity gives
\[
C_{a,b}(x)=a\vee S_{a,b}(x),
\qquad
S_{a,b}(x)=b\wedge C_{a,b}(x).
\]
Consequently,
\[
S_{a,b}(x)=S_{a,b}(y)
\quad\Longleftrightarrow\quad
C_{a,b}(x)=C_{a,b}(y)
\]
for arbitrary windows. The expressions themselves need not be equal
when \(a\not\le b\); the equality relations are equivalent.

Do not identify either raw endpoint with the book's stronger single-value
relation \(Q(a,b,r,v)\), which requires
\(b\wedge v\le r\le a\vee v\). For a Boolean OR node of true value,
default bounds and window (true,true), an immediate cut returns
(false,true); the lower endpoint fails \(b\wedge v\le l\).
The paired theorem remains correct. The book bridge is through squash
observations and full-window values unless an additional theorem proves
another conversion.

## 6. Proof repairs and independent boundary examples

These are source-specific issues to preserve when the formalization
reaches this chapter. None is evidence that the corrected theorem has
already been checked in Lean.

### D27C-2: the long proof names the wrong child-call window

JIAF p.107 defines \(A_i\) after iteration \(i\), then describes child
\(j\)'s call as using \(A_j\). Algorithm 2 calls that child with
\(A_{j-1}\) and only afterward updates
\(A_j=A_{j-1}\vee l_j\). The proof's trace identification is false.

A small witness is a Boolean OR root with one true leaf, empty cache,
default internal bounds, and window (false,true). The actual child
call uses lower window false; the post-return value \(A_1\) is true.

The equation needed by the proof is nevertheless recoverable. Write
\(A=A_{j-1}\) and \(B=b\wedge c_U\). The actual recursive induction
hypothesis is
\[
B\wedge(A\vee l_j)=B\wedge(A\vee u_j).
\]
Proposition 2 gives \(l_j\le u_j\). Thus
\[
A_j\vee l_j=A\vee l_j,\qquad
A_j\vee u_j=A\vee u_j,
\]
which proves the equality at \(A_j\) used to derive equation (6).
This is a missing algebraic justification, not a counterexample to
Proposition 3. The cutoff index \(A_{k-1}\) on p.108 is correct,
including a cut before the first child; do not “repair” it to \(A_k\).

### D27C-3: both proofs omit an explicit exact internal-node branch

The proofs of Propositions 2–3 first handle leaves, then proceed as
though every nonleaf enters the child loop. Algorithm 2 also returns
immediately at an internal node when \(c_L=c_U\). Handle the equality
test before the leaf/internal split. Coherence/admissibility brackets
the true value between equal endpoints, so the answer is exact and the
cache is unchanged. This fills the proof case without changing the code
or weakening the theorem.

### Useful loop invariant for an independent formal proof

At an OR node put \(A_0=a\vee c_L\) and \(B_0=b\wedge c_U\).
After \(j\) completed child calls, let \(L_j,U_j\) be the joins of their
respective endpoints. Then
\[
A_j=A_0\vee L_j,\quad B_j=B_0,\quad
B_0\wedge(A_0\vee L_j)=B_0\wedge(A_0\vee U_j).
\]
Derive each step from the recursive result at the actual pre-update
window and distributivity. The no-cut case combines all child brackets;
the cut case restores \(c_U\) and uses
\(B_0\le A_0\vee L_j\). Meet/join duality gives the AND proof, with
the two squash conventions related as above.

This is an original proof route for the recovered contract, not a
claim that an unverified transcription of the printed proof suffices.

### Additional checked examples to retain when implementing

The following examples are bounded mathematical witness targets, not a
request for a separate testing framework.

| Case | Required observation |
|---|---|
| Boolean exact leaf, absent and present cache | Exact result; cache unchanged on the early-return branch. |
| Exact nonleaf cache/initializer | Immediate exact return without visiting a child. |
| Initial cutoff before the first child | Correct restored interval and stored result. |
| Cut after a visited prefix | The unvisited side's bound is restored to the old endpoint. |
| Last child makes the window collapse | No extra post-loop cutoff/reset; retain the tighter completed result. |
| A diamond DAG with a shared descendant | Later branch sees the cache from the earlier branch; output and state theorem both apply. |
| Consecutive OR nodes and consecutive AND nodes | No alternation assumption sneaks into the graph theorem. |
| A product Boolean lattice and incomparable windows | All-window squash theorem uses partial order, not totality. |
| Single-value cache flag failure | Retain the distinction between a scalar squash-correct answer and a global interval. |

For the last row, Figure 1 right supplies a compact example over
three-bit Boolean vectors, with bitwise meet/join. Let R be AND of A
and B; A is AND of leaf111 and C; C is OR of leaves110 and001; B is
OR of leaf001 and D; D is AND of leaves010 and001. The true root
value is001. The source's uncached single-value algorithm at window
(010,110), with its default admissible heuristic, returns010, which
is incomparable with001. It cannot be treated as either a global
lower or a global upper bound merely by copying a total-order cache
flag convention. The graph/cache implementation witness itself remains
Algorithm 2; reproducing every Algorithm 1 development is unnecessary
for this bounded extension.

## 7. Semantic and architectural integration boundary

The graph value unfolds to a finite tree **with a role at each internal
node**. The source graph permits nonalternation; the book's rose-tree
maxmin/minmax and supinf/infsup evaluations alternate roles. On
alternating graph inputs, prove the corresponding value bridge after
unfolding, with the appropriate root role. For general role-labelled
trees, a value-preserving alternating encoding may insert unary nodes
where needed, since a unary meet/join preserves its child value.
Such an encoding changes execution and cannot justify identical
resource counts.

The source's childless node is a leaf evaluated by \(e\). The book
also has an explicit internal constructor Nd[] whose value is bottom
or top according to the role. Do not erase that constructor silently
in a tree bridge. Either state the no-empty-internal premise for a
direct correspondence or give a separate value-preserving translation
to a graph leaf with the relevant extremal value, acknowledging the
changed traversal.

The operational witness should reuse established finite-map and
state/resource composition interfaces when implementing, with a
source-to-definition equation for each branch in §4. Value agreement
with an unfolding or with an existing tree search is not an equality
of cache operations, recursive visits, lattice operations or total
cost. Cache effects are part of the computation; \(v(n)\) is its
independent specification, never its implementation oracle.

No \(O(\lvert N\rvert+\lvert E\rvert)\) time bound, universal speedup,
one-visit-per-node property, finite-lattice restriction, arbitrary
cyclic-game theorem or cache-capacity theorem is asserted by the book's
paragraph or by the recovered correctness result. The paper's
experimental counts do not provide any such theorem. Keep the
resource witness connected to the actual recurrence without inventing
a complexity milestone.

## 8. Inventory reconciliation and remaining work

The preserved pre-recovery file is:

**../reviews/source-inventories-before-cache-recovery/chapter27-obligations.md**

- Size: **65,605 bytes**.
- SHA-256: **4a7c5a4675822ac7ed0dad125be33b4eb637410ed04beaf8cc07da4672b22ea3**.

The precise changes to the current inventory are:

| ID/section | Clarification |
|---|---|
| Sources table | Add the exact short-paper and accessible long-proof identities and point to this complete provenance. |
| C27-067, C27-179 | Replace the unresolved-source pointer with the recovered fixed-DAG/node-key construction, retaining the same scope and key/evaluator conditions. |
| C27-180 | Mark primary-source recovery as available; retain implementation/theorem correspondence as future work. |
| C27-181 | Record arbitrary AND/OR labels, bounded distributive values and the explicit finite-DAG/progress correction with its counterexample. |
| C27-182 | Name Algorithm 2's stateful paired recurrence and exact operational branches. |
| C27-183 | Replace the provisional scalar minimum observation by the complete pair/state/bracketing/squash contract, including leaf exactness and arbitrary windows. |
| C27-184 | Record coherent cross-window reuse, global refinement, and carefully qualified tree/value bridges. |
| C27-185 | Retain executable correspondence, source-proof repairs and resource integration, with no unsupported complexity promise. |

All **185 existing IDs are preserved and queued**. Earlier scope-audit and
scope-reconciliation documents retain their historical as-of hashes;
this recovery does not rewrite them. The only remaining access limitation
is the exact HAL v2 PDF: its content cannot be compared with the read
long version. The official IJCAI construction and the complete relevant
JIAF proofs are available, so this is no longer an unresolved mathematical
source-recovery gap.

The corrected domain, recurrence, invariant, proof repairs, bridges and
counterexamples remain **unimplemented and unaccepted**. This task
performed no Lean edit, compiler/build command, ticket transition, Git
operation, acceptance change, or remote write.

The post-clarification inventory hash is recorded below after the
bounded edit; this note's own hash is reported to the parent separately
to avoid a self-referential digest.

Post-clarification inventory: **68,420 bytes**, SHA-256
**87ba6c9cbca1df75012cc594668ea1c7c0b76cfb76ea8e1cee9f7276e4e298e6**.

[I-record]: https://www.ijcai.org/proceedings/2022/661
[I]: https://www.ijcai.org/proceedings/2022/0661.pdf
[J]: https://ci.mines-stetienne.fr/pfia2022/conferences/jiaf/actes/actes_jiaf_2022.pdf
[H-api]: https://api.archives-ouvertes.fr/search/?q=halId_s%3Ahal-03656224&fl=*&wt=json
[H-v2]: https://hal.science/hal-03656224v2/document
[H-rights]: https://about.hal.science/en/hal-authorisation-v1/
[I-rights]: https://ijcai.org/past_conferences/
