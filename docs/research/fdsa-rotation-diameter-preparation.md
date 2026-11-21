# Exact rotation diameter: unqualified preparation

FDSA-5-92 remains open: every pair of common-size binary-tree shapes must have
distance at most 2N−6, and an explicit pair must attain that bound, for N≥11.
This paper preserves the mathematical preparation by
`/root/recovery_book_inventory`, begun 18 November 2026. Its geometric arguments,
family formulas and proposed proof decomposition remain **unqualified paper
work**. The receiving curation adds no Lean theorem and makes no new primary
reading claim. Current requirements and receiving status are tracked in [CTB](../textbooks/CTB.json). Cumulative source integration is tracked under [issue #660](https://github.com/VladimirMarko/conaled/issues/660); FDSA-5-92 remains an open mathematical obligation. This paper is not a Lean dependency or a receiving validation receipt.

The later sections [Concrete finite obstruction](#concrete-finite-obstruction)
and [Tree-diagonal bridge](#tree-diagonal-bridge) preserve the subsequent complete
literal tables and tree realization. They replace the earlier missing-table
obligation for those explicit objects. The lost memo itself was not recovered,
and identification with the primary figure-defined families remains unresolved.

## Primary sources and attributed reading

The original author read all 28 pages and visually inspected all 14 figures of
Lionel Pournin, *The diameter of associahedra*,
[arXiv:1207.6296v4](https://arxiv.org/abs/1207.6296v4),28 March 2014,
[manuscript](https://arxiv.org/pdf/1207.6296v4),
[DOI](https://doi.org/10.1016/j.aim.2014.02.035).
The acquired PDF had 964,617 bytes and SHA256
`2f5a4ea8866e60b31a765549e48f3620dae34c0b75158cc9a1d53f9bbe1f295b`.
The 14 figures were inspected on pages 7,9–13,15–16,18–20,23,25–26.

The same author read printed pp.647–654 (the first eight PDF pages) of
Sleator, Tarjan and Thurston, *Rotation Distance, Triangulations, and Hyperbolic
Geometry*, JAMS 1(3),1988, using OCR and visual inspection of the scanned pages:
[author page](https://www.cs.cmu.edu/~sleator/papers/Rotation-Distance.htm),
[PDF](https://www.cs.cmu.edu/~sleator/papers/rotation-distance.pdf).
The 35-page PDF had 12,392,846 bytes and SHA256
`141a192a506d2cfec90f75a7da8689b808bb1854acfc6328943a18644a549894`.
PDF pages 9–35 were not read or used. No hyperbolic lower-bound theorem is assumed.
Downloaded primary bodies/renders are external research inputs. These historical
reading identities do not assert current availability of old scratch copies.

## 1. Exact target and conventions

The canonical owner is the [Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md), row **FDSA-5-92**, under CTB-24. It demands the exact maximum rotation distance **2N−6 for binary trees with N internal nodes, N≥11**. FDSA-5-91's constructive 2N−2 connection bound does not establish this stronger claim. Difficulty and citation to external papers do not remove FDSA-5-92 from whole-book completion.

Use separate variables throughout the implementation to avoid the papers' conflicting uses of `n`:

| Object | Parameter/count | Target range |
| --- | --- | --- |
| Ordered rooted binary tree | N internal nodes | N≥11 |
| Convex polygon | m=N+2 vertices | m≥13 |
| Associahedron | d=N−1=m−3 dimension | d≥10 |
| Triangulation | m−3=N−1 interior diagonals; m−2=N triangles | — |
| Tree external leaves | N+1=m−1 | — |
| Desired distance | 2N−6=2m−10=2d−4 | — |

Pournin explicitly gives the dimension/polygon/tree conversion on pages 1–2. A triangulation there is the **entire edge set, including boundary edges**; its cardinality is 2m−3. A flip replaces exactly one interior diagonal in its unique incident quadrilateral. Polygon vertices have a fixed clockwise cyclic order. Distances are between labelled triangulations on the same polygon, not equivalence classes under independent rotation/reflection. A simultaneous dihedral relabelling of both endpoints can preserve distance; independently relabelling endpoints is not such a theorem.

The ordinary polygon model starts at m=3, hence N=1. The empty tree has no ordinary convex polygon counterpart; handle it separately if the general distance foundation covers N=0. The mandatory sharp theorem only needs N≥11.

## 2. Existing local source and remaining correspondence

The initial inventory at donor `117342ce432b0e138a78ab615289c35ae07decd4`
preceded the mixed-distance increment. Its reusable partial-rotation, position,
normalization and 2N−2 route laws remain described in
[the primitive rotation note](fdsa-tree-rotations.md).
The accepted donor now supplies [mixed execution](../../Applications/Trees/Rotations/Mixed.lean)
and [attained distance](../../Applications/Trees/Rotations/Distance.lean), documented
in [the minimum-distance note](fdsa-rotation-distance.md).
`applyMoves?` checks each partial move on its evolving state. `distance_spec`
provides an attained legal trace, `distance_le_length` compares every legal trace,
and `Shape n` is the fixed-node-count subtype of `BinaryTree Unit`.

These are the foundation for the new sharp theorem, not that theorem itself.
Right-only listification optimality still does not imply shortest mixed distance.
Arbitrarily labelled trees are connected only when their complete inorder lists
agree; equal size or equal label set is insufficient. The empty tree has its own
size-zero distance case. A polygon correspondence still needs a distinguished
root boundary edge and preservation of adjacency **in both directions**, hence
trace lengths and distance. Simultaneous label symmetry is different from
independently relabelling the two endpoints.

## 3. Pournin pages 1–5: distance and geodesic infrastructure

The paper's main family is A_m, a pair of m-gon triangulations. Its announced lower-bound recurrence for m>12 is

`δ(A_m) ≥ min {δ(A_(m−1))+2, δ(A_(m−2))+4, δ(A_(m−5))+10, δ(A_(m−6))+12}`.

The complete case analysis and actual base values have now been read; see sections 6–8 below. In particular, the distances of A_m are **not** the small associahedron diameters at every size. Do not substitute a remembered diameter sequence as a certificate for the specified A-family.

The elementary upper bound (Lemma 1) is δ(U,V)≤2m−10 for m>12, cited to STT Lemma 2. Pournin also uses the following geodesic facts cited to STT Lemma 3:

- If one flip from U introduces an edge of the endpoint V, **some** shortest U→V path begins with that flip (Lemma 2).
- An edge common to the endpoints remains in **every** shortest path (Lemma 3). Applied to subpaths, an edge cannot disappear and later reappear along a geodesic.
- Lemma 4 allows a first flip whose introduced edge occurs at an intermediate state of a chosen geodesic, by replacing its prefix while retaining shortest length.
- Theorem 2 handles a prescribed path starting at the geodesic's initial vertex. If one intermediate state of the geodesic contains **all edges introduced by that prescribed path**, the endpoint distance falls by exactly the prescribed path length. Formalization must derive the needed length inequalities before natural-number subtraction.

These are mathematical dependencies, not acceptable assumed theorem fields. The relevant STT proofs must also be inspected and implemented if used. An elementary non-leaving-face/normalization construction is a promising common reusable abstraction, subject to that source reading.

## 4. Pournin pages 5–10: vertex deletion and forced incidence

### 4.1 Exact deletion, not arbitrary vertex erasure

Delete a vertex a **toward its current clockwise successor b**. For every edge, substitute b for a, omit the collapsed boundary edge {a,b}, and form a set so duplicate edges merge. For m≥4 the result is a triangulation of the (m−1)-gon (Proposition 2). Its counting proof loses exactly the collapsed edge and one duplicate: the unique boundary triangle has third vertex c, and {a,c}, {b,c} become the same edge. Deletion preserves the cyclic noncrossing relation because a,b are adjacent.

The **link** of boundary edge {a,b} is its unique third triangle vertex. A flip is incident to that boundary edge exactly when its link changes. Theorem 3 proves that a path of k flips, j of them incident to {a,b}, projects after deletion to a path of exactly k−j flips once unchanged successive states are removed. Each original flip either remains one genuine quadrilateral flip or collapses to equality; the second case is exactly boundary incidence.

This suggests a reusable path-contraction theorem parameterized by a map that sends steps either to a genuine step or equality, together with a predicate characterizing collapsed steps. A nonexpansiveness inequality alone would lose the exact additive lower bounds needed later.

### 4.2 The quantifier in Θ is consequential

Pournin's Θ(P,a) is the **maximum number of incident flips among all geodesics** joining the endpoints P. It is neither the minimum nor a count along an arbitrarily selected geodesic. Corollary 1 gives `δ(P) ≥ δ(P\a)+Θ(P,a)` by selecting a maximizing geodesic and applying path contraction.

One can avoid a large explicit maximum API by proving existential statements such as “there exists a geodesic with at least k incident flips,” and using their negations as universal bounds. This is a proposed simplification, not permission to weaken the quantifier. Bounded incident counts and existence of geodesics justify any maximum definition.

### 4.3 Local incidence lemmas

Theorem 4 gives two boundary edges (a,b),(c,d) for which certain edges determined by their initial links are distinct and cross the opposite final-link edges. The two incidence maxima cannot both be below 2. If each boundary link changed exactly once on a geodesic, crossing exclusion forces each change to occur no later than the other; they would be the same flip, requiring it to delete two distinct edges.

Theorem 5 specializes to consecutive a,b,c. If a,c and the two initial link vertices are pairwise distinct and {a,c} belongs to the target, then at least one of the two boundary-edge incidence maxima is ≥2. In the one-change case for the first edge, the second link is forced through three distinct values.

Corollary 2 treats five consecutive vertices a,b,c,d,e, three specified distinct initial links, and a target fan containing {a,e},{b,e},{c,e}. Deleting b,c,d gives a distance drop of at least **5 = 2+2+1**. Its adaptive deletion order requires a lemma that deletion of this contiguous block gives the same final pair. It is not a general claim that arbitrary vertex-deletion operators commute.

## 5. Pournin pages 11–12: initial family construction and caveats

The base zigzag Z_m has interior edges forming a path alternating left/right turns and is specified relative to vertex 2 (Figure 4, now visually inspected). Write `bar(k)=k+floor(m/2)` modulo m. The visible diagonal sequence starts `{2,4}, {1,4}, {1,5}, {0,5}, {0,6}, …`. A proposed explicit formula for the m−3 diagonals, indexed by j=0,…,m−4, is `{2−r,4+r}` for j=2r and `{1−r,4+r}` for j=2r+1, with endpoints reduced modulo m. This is an inferred implementation formula, **not yet checked by computation or proved equivalent to the paper's figure-defined family**. It provides a concrete route to prove noncrossing, distinctness, and parity identities without treating a diagram as an axiom.

For the family on m vertices, start with **Z_(m+4)**:

- A⁻_m deletes original vertices 0,1,bar(0),bar(1), then relabels survivors clockwise 0,…,m−1, preserving the label 2 of the original vertex 2.
- A⁺_m deletes original vertices 4,5,bar(4),bar(5), then relabels survivors clockwise with original vertex 2 receiving new label 1.
- Equal new labels identify the two resulting polygons; A_m is the resulting pair.

The bars refer to the **original (m+4)-gon**. Keep vertex identities during all four deletions; do not recompute antipodes after shrinking the polygon. Each deletion still collapses toward the current clockwise successor. Relabel only after the designated deletions. This is an implementation inference from the stated construction and needs explicit verification against the diagrams/definitions.

For m>8 the displayed pair contains endpoint combs connected by a zigzag, but small values need separate treatment: at m=10 one connecting zigzag has only one edge and the other has vanished; at m=9 endpoint combs overlap in one tooth; below 9 combs shrink or disappear. The two m=3 triangulations coincide. Generic large-m pictures cannot justify the small base cases or recurrences at their boundary.

## 6. Auxiliary families and exhaustive recurrence cases (Pournin pp. 13–21)

### 6.1 Deletion isomorphisms for A

Proposition 3 proves that A_m with vertex 1 deleted is isomorphic to A_(m−1), for m>3. Its exhibited map **reverses** cyclic order and swaps the two endpoints: relabel counterclockwise so old vertex 2 becomes new 3. Therefore the reusable symmetry result must allow simultaneous reflections and endpoint exchange, not just clockwise shifts. Similarly A_m with 3 then 1 deleted is isomorphic to A_(m−2).

Theorem 6: for m>3, Θ(A_m,1)≥2 gives δ(A_m)≥δ(A_(m−1))+2. Theorem 7: for m>5, Θ(A_m,3)≥3 gives δ(A_m)≥δ(A_(m−2))+4. The extra 1 in the latter comes from different links of boundary edge {1,2} after deleting 3: the initial link is 5 for m=6,7 and 6 for m>7, whereas the final link is 4. The small-size split is real.

### 6.2 B and C use an ear removal after actual flips

For q>6, construct B⁻_q from A⁻_(q+1) by flipping **{2,5}, then {2,4}, then {2,6}**, in that order. The last flip introduces {1,3}. Remove the two boundary edges {1,2},{2,3} and vertex 2 (the common ear), leaving {1,3} as the new boundary edge. For B⁺_q remove the same ear from A⁺_(q+1). Relabel survivors clockwise, keeping old vertex 3 labelled 3. Define C⁻_q by flipping {4,6} in B⁻_q; C_q shares B⁺_q as its second endpoint.

These are **legal state-dependent flip schedules**; stating that all listed edges occur in the initial triangulation does not by itself certify legality at their execution times. Ear removal here is naturally a restriction to a face containing {1,3}, not an arbitrary application of deletion that happens to preserve distances.

Theorem 8 handles exactly the complementary case for m>7:

`Θ(A_m,1)≤1 ∧ Θ(A_m,3)≤2`

implies the existence of P in {B_(m−1), C_(m−1)} with

`δ(A_m)=δ(P)+3` and `Θ(P,3)≤1`.

The boundary {1,2} changes link once, forcing the flip {2,6}→{1,3}. At that intermediate state, the quadrilateral on {3,4,5,6} contains one of {3,5} and {4,6}. That choice specifies the order of the first two flips. Theorem 2 permits moving the corresponding three-flip sequence to the beginning of a geodesic. The common-edge theorem then preserves {1,3}; removing its ear gives the smaller geodesic. **Every** smaller geodesic can be lifted back and prefixed by the three flips. Since one prefix flip is incident to {3,4}, this establishes the bound on Θ(P,3). One lifted chosen suffix is insufficient to establish that maximum bound.

Proposition 4 (m>7) combines these exhaustive cases:

`δ(A_m) ≥ min {δ(A_(m−1))+2, δ(A_(m−2))+4, δ(B_(m−1))+3, δ(C_(m−1))+3}`.

### 6.3 Costs for B and C

For q>11 and Θ(B_q,3)≤1, Lemma 5 gives a cost of **4** for deleting 4,5. A unique flip incident to {3,4} produces an intermediate triangulation; split the geodesic there. On the first portion, different links force one lost flip. On the second, Theorem 5 and another link change force three. Combine the two deleted-path distances by the triangle inequality. One cannot replace this split-path argument with an unsupported claim that four specific incidents occur together on a single arbitrarily chosen deletion path.

After these deletions, Theorem 9 uses Corollary 2 at the three remaining consecutive vertices 0,1,2, contributing **5** more. Their links are 8,7,6; the target has {0,3},{1,3},{3,q−1}. The final pair is isomorphic to A_(q−5). Thus

`δ(B_q) ≥ δ(A_(q−5))+9`.

For q>11 and Θ(C_q,3)≤1, Theorem 10 uses Theorem 5 at {3,4},{4,5} to force Θ(C_q,4)≥2. Delete 4 at cost **2**, then delete 0,1,2 at cost **5**. The final pair is isomorphic to A_(q−4), yielding

`δ(C_q) ≥ δ(A_(q−4))+7`.

The dimension restrictions ensure that the indicated boundary-edge links have not merged into the remote comb. The paper uses the arithmetic `ceil(q/2)+3≤q−3`, `ceil(q/2)+3<q−2`, and `8≤ceil(q/2)+2`. Diagrams require additional small q=12,13 attention: Figure 10's upper-right generic drawing is only valid for q>13; its bottom row treats q=12,…,15.

Theorem 11, for m>12, now gives exactly the four-offset A recurrence. The +12 branch is **3+9** through B_(m−1) and A_(m−6). The +10 branch is **3+7** through C_(m−1) and A_(m−5). Keep these offsets paired correctly.

## 7. Source finite bases and the unresolved Q10 correction

The paper gives a combinatorial proof of the required finite lower bounds. It does **not** rely on a machine enumeration of all m≤12 diameters for its main theorem.

| Polygon vertices m | Source claim δ(A_m) | Proof location and relevant method |
| --- | --- | --- |
| 3 | 0 | Proposition 5: identical triangle |
| 4 | 1 | Proposition 5: one differing diagonal |
| 5 | 2 | Proposition 5: each of two flips introduces a final diagonal |
| 6 | 4 | Proposition 6: no first flip introduces a target diagonal, then three differing diagonals remain; explicit 4-flip route |
| 7 | 5 | Proposition 6: delete vertex 0, different links give +1 over A_6; explicit 5-flip route |
| 8 | 7 | Proposition 6: Theorem 4 forces ≥2 incidents at 0 or 4; either deletion gives A_7; explicit 7-flip route |
| 9 | 8 | Theorem 12 lower bound and Proposition 8 fan route |
| 10 | 10 | Same |
| 11 | 12 | Same |
| 12 | 14 | Same |

Proposition 7 supplies the auxiliary finite lower bounds `δ(B_q), δ(C_q) ≥ 2q−11` for q=8,9,10,11:

- q=8: both endpoint pairs have five distinct interior diagonals and admit monotone target-edge introduction paths, hence distance 5.
- q=9: delete vertices 1,2 at cost 3, leaving a Q pair with four distinct interior diagonals; bound 3+4=7.
- q=10: delete 1,2 at cost 3. Q has five distinct interior diagonals. The original preparation copied a no-first-target-edge argument for the extra unit, but the retained independent correction below reports an explicit target-introducing first flip in both Q10 variants. This argument cannot be used as written; the needed Q lower bound 6, and hence total 9, require the repaired finite analysis.
- q=11: delete 0,1,2 at cost 5. Q again has five distinct interior diagonals and no target diagonal can appear on the first flip; total 5+6=11.

The B/C variations lead to the finite Q drawings in Figure 12; these need concrete edge-set checks once the definitions are established. A proof that each flip removes at most one currently differing diagonal supplies the basic distance lower bound. A verified “no final diagonal on the first flip” premise increases it by one where it actually holds, but the Q10 correction prevents using that premise uniformly. These small generic lemmas do not remove the obligation to verify each finite case.

For m=9,…,12 use Proposition 4 and the B/C lower bounds; for m≥13 use Theorem 11 and strong induction. The paper writes a formally loose induction hypothesis mentioning A_i for i=0,1,2, although the family is only defined for i≥3. Restrict the IH to the actual defined range. For natural-number arithmetic, state the lower bound as `2*m ≤ δ(A_m)+10` or explicitly work over integers; do not silently use truncated subtraction in rearrangements below m=5.

**Possible target-preserving simplification:** the mandatory theorem only needs m≥13, whose largest offset is 6, so a lower-bound induction may begin at m=7. One could prove the sufficient weaker seeds δ(A_7)≥4 by the four differing diagonals and δ(A_8)≥6 using Theorem 4/deletion to A_7, then carry out Proposition 4 for m=9,…,12. The exact small values above remain the correct source facts; the simplified proof would omit unnecessary equality proofs, not weaken FDSA-5-92. This suggestion is unimplemented and must retain every needed finite family/deletion identity.

### Retained independent Q10 conflict and proposed repair

The earlier checkpoint058 conversation-recovery draft reports a specific
independent correction to Pournin Proposition 7, p.23 / Figure 12. In **both**
minus Q10 configurations B and C, diagonal `{0,7}` has adjacent triangles
`{0,3,7}` and `{0,7,9}`. Its quadrilateral flip introduces `{3,9}`, reported to be
an edge of the plus target. Thus the retained claim that neither Q10 variant can
introduce a target edge on its first flip conflicts with this explicit calculation.
The no-first-target claim must not be ported into a proof without resolution.
The cited adjacent triangles determine opposite vertices 3 and 9, hence that
local flip shape; membership of those triangles and the target edge in the exact
constructed families still needs the recorded or recomputed family tables.

The proposed repair is that this target-introducing first flip is unique and,
after taking it, no second flip introduces another target edge. Starting with
five missing target diagonals, that delay would still force at least six flips.
The independent memo reportedly contained both variants' complete first- and
second-flip tables; the recovery draft does **not** contain those tables. It
reported that Q11's no-first-target assertion checked out. These are attributed,
unqualified findings, not newly reconstructed or accepted finite certificates.

The missing independent memo was reported as 35,510 bytes / 307 lines, SHA256
`10bba29b1bf189c23b3d7b2f48438d999f0051c5e985b84aa62394b86e94dbc7`.
The root had not fully read it or its companion reading record before the loss.
Its author reported reading the full Pournin text and selected Pournin/STT page
images; the surviving draft supplies that attribution, not the original images
or complete reading record. This receiving curation adds no primary reading.

The same relay reports an A13 construction check: both ten-diagonal sets and
both eleven-entry split tables were checked through Z17, deletions and relabelling,
including fourteen edge images. Those tables are absent here. A construction
check does not prove distance 16. The proposed restricted induction used
`A7 ≥ 4`, `A8 ≥ 6`, `B/C8–11 ≥ 5/7/9/11` (with the Q10 repair), then
`A9–12 ≥ 8/10/12/14` via Proposition 4, and Theorem 11 for polygon size at least
13 with predecessors at least 7. This remains an alternative architecture to
verify, including the claimed no-first-target table for A8 and every deletion
identity; it does not certify the finite seeds in the preceding table.

Before formalization, reconstruct the concrete Q10/Q11 edge sets and flips,
check the two-step repair, and reconcile the older independent finding with the
later complete-paper preparation. Keep the unresolved conflict explicit rather
than silently choosing the later report or assuming the missing tables survived.

## 8. Complete-paper scope and textual cautions

Proposition 8 (pp. 24–25) gives δ(A_m)≤2m−10 for every m>8 by routing both endpoints through the fan at vertex 3. The A⁺ endpoint already has four incident diagonals there; the two costs are m−7 and m−3. Thus A_m is **not** always a diameter pair at small sizes: for d=6,7,9 (m=9,10,12), its distance is one below the cited diameter. The source's small-dimension diameter list is `0,1,2,4,5,7,9,11,12,15` for d=0,…,9. That list is discussion/context, not an additional dependency for FDSA-5-92.

Section 6.2 constructs a different, more symmetric D-family and refutes the suggested extremality of that family. Proposition 9 gives a concrete 14-flip/17-flip route reduction `δ(D_m)≤δ(D_(m−16))+31` for m>19, using shared diagonals to strip equal subregions. Consequently its asymptotic slope is at most 31/16. This warns against replacing A by a visually simpler symmetric zigzag/comb family without a new proof. The D-family is not needed for the mandatory sharp theorem.

Section 6.3 discusses possible extensions and explicitly notes that vertex deletion need not preserve a triangulation for more general point configurations, even in the plane with interior points. Keep the reusable deletion interface's convex cyclic-polygon assumptions; do not generalize it from this source to arbitrary triangulations. The last page is references; all reference entries have been read, without claiming to read all cited works.

Apparent source slips to resolve by the stated definitions and independently checked sizes:

- Page 15's alternative C⁻_q construction says it flips three edges in A⁻_q and then removes an ear. The established B/C definitions and the proof of Theorem 8 require **A⁻_(q+1)** to produce a q-vertex result. This indexing slip is visually present in the PDF, not merely text extraction. Prefer the unambiguous definition C⁻_q=flip_{4,6}(B⁻_q) until the alternative is separately proved.
- Page 22 says “A_6 is not less than 5” immediately after deriving δ(A_7)≥δ(A_6)+1; context and the displayed route show **A_7** is intended. Do not propagate that sentence as a theorem.
- Strong-induction bounds must respect m≥3 as noted above.

## 9. STT elementary arguments actually read (printed pp. 648–654)

### 9.1 Conventions and graph correspondence

STT §2.1 counts **internal** tree nodes; a tree of size N has N+1 external leaves. Its §2.2 maps the N internal nodes to N triangles in a polygon with N+2 vertices. The polygon has a distinguished root boundary edge and orientation. Non-root-edge vertices correspond to the inorder sequence, with a recursive triangle decomposition encoding the left/right subtrees. Lemma 1 states the graph isomorphism between N-node tree rotations and flips of the (N+2)-gon.

The paper then explicitly **changes its use of n** in §2.3 to count polygon vertices. This variable switch is the main reason to maintain N/m/d separately. Its Figure 4 caption calls the hexagon graph `RG(6)` although the text identifies it as `TG(6)` and the established isomorphism is `RG(4)`; use the explicit definition rather than copying that caption.

### 9.2 Fan routing and the sharp upper bound

STT Lemma 2 (printed p. 652) proves the polygon bound directly:

1. Let `deg_T(x)` count **interior diagonals**, not all boundary-inclusive incident edges. If this count is below m−3, an appropriate flip introduces one additional diagonal at x. Iterating yields the unique fan at x in exactly `(m−3)−deg_T(x)` flips.
2. Route U to that fan, then reverse V's fan route. Its length is `2m−6−deg_U(x)−deg_V(x)`.
3. Each triangulation has m−3 diagonals, so the sum of its diagonal degrees is 2(m−3). Across U,V the total is 4(m−3). If all m combined degrees were at most 3, the total would be at most 3m, contradicting m>12. Thus some x has combined degree at least 4.
4. The route length is at most 2m−10. Transfer with m=N+2 to obtain 2N−6 for N≥11.

This proof needs no real-valued average or geometry in Lean: a finite sum and integer pigeonhole argument suffice. The fan-extension step still needs a constructive local quadrilateral proof and a termination measure; do not place it in an assumed law field. The bound's threshold is essential: m=12 admits diameter 15 while 2m−10=14, as the primary source's finite table and Pournin's discussion report. Likewise N=10 is outside the required sharp range.

### 9.3 Normalization toward a fixed diagonal

STT Lemma 3 (printed pp. 652–654) normalizes any triangulation T toward a diagonal e={l,r}, choosing r as a fixed endpoint. Include e; retain all edges not crossing e; replace each crossing diagonal {a,b} by the spokes {a,r},{b,r}; take a set, together with boundary edges. Some spokes are boundary edges and duplicates merge. This is naturally expressed in Pournin's full edge-set convention, avoiding the paper's informal use of “diagonal” for all generated spokes.

Required proved properties of this construction are:

| Property | Purpose |
| --- | --- |
| The output is a triangulation containing e | Defines a genuine normalization function |
| If e belongs to T, normalization fixes T | Endpoint preservation/retraction |
| A flip maps to equality or a single flip | Path-length nonincrease after compression |
| If a flip inserts or removes e, the normalized endpoints coincide | Strict savings when an edge is entered or left |
| Noncrossing edges of the input remain | Common-face compatibility and local arguments |

The source describes the flip case analysis as straightforward but does not eliminate it. Prove it using cyclic-order cases or the crossed chain of triangles, including endpoint-sharing and boundary-spoke cases.

For Lemma 3(a), start with an arbitrary path U→V where a legal first flip would introduce a final diagonal e. Normalize the entire path toward e and prepend that legal flip U→N(U). Since the original path must enter the e-containing face at least once, one original step collapses. The extra prefixed step is offset by that collapse, so a shortest original path yields a shortest new path starting with the prescribed flip.

For Lemma 3(b), any path that removes a diagonal common to its endpoints must later reinsert it. Normalization collapses at least these two distinct steps. Thus such a path exceeds the shortest length by at least 2; in particular **every** geodesic preserves every common diagonal. If removal occurs after an initial prefix, apply the argument from its first removal or normalize the whole path and count both crossings. This supplies Pournin Lemmas 2 and 3 without any hyperbolic premise.

Theorem 8 additionally needs an **ear-face isometry**: triangulations sharing the ear chord {1,3} correspond to smaller triangulations after removing vertex 2; flips within that face correspond one-for-one, and any smaller path lifts by adjoining the fixed ear. Together with common-edge persistence this preserves geodesics and permits the universal suffix replacement used to bound Θ. A general graph-retraction lemma may supply part of this proof, but the ear adjacency correspondence must still be established.

## 10. Proposed implementation dependency map

These are mathematical components, **not** allocated tickets, approved source scopes, or a proposal to redefine the target. Keep FDSA-5-92 mandatory while fitting coherent increments into the ordinary example/implementation/review/checkpoint process.

| Stage | Concrete outcome | Dependencies and reuse |
| --- | --- | --- |
| A. Mixed rotation distance | Existing `RotationMove`, `applyMoves?`, attained minimum and `Shape n`; finite maximum/attainment interface for the new diameter theorem remains to connect | Reuse `Mixed.lean` and `Distance.lean`; FDSA-5-91's 2N−2 route supplies connectivity. Right-only optimality still concerns a different problem. |
| B. Cyclic polygon triangulations | Finite labelled vertex/edge model; crossing, boundaries, triangle/link uniqueness, m−3 diagonals, quadrilateral flip | Prefer finite cyclic-order combinatorics; no analytic convexity or associahedron realization is needed for the requested tree theorem. Prove that the chosen model has exactly the paper's triangulations. |
| C. Rooted tree/flip correspondence | Size-preserving bijection, adjacency equivalence, trace transfer, distance equality | Root boundary edge, ordered left/right children, fixed inorder or unlabelled shapes. Reuse the existing tree carrier rather than a second unrelated binary-tree type. |
| D. Universal upper bound | Fan-extension trace, finite degree count, 2m−10 bound for m≥13, then tree bound | B, A/C. This is already a coherent theorem even before the lower bound, but does not close FDSA-5-92 alone. |
| E. Path infrastructure | Shortest subpaths, triangle inequality, contraction with exact collapsed-step count, isomorphism invariance, common-ear restriction/lift | Reuse/generalize existing legal trace structure; finite graph/path facts should not be encoded separately in each family proof. |
| F. Normalization | Concrete diagonal normalization and local flip behavior; target-edge-first and common-edge geodesic lemmas | B,E; STT Lemma 3. Boundary-inclusive edge sets simplify spokes. |
| G. Vertex deletion | Concrete clockwise-neighbor contraction, triangulation preservation, exact incident-step characterization; Θ/existential-geodesic lower-bound principle | B,E. Separate this operator from normalization and from ear restriction. |
| H. Forced-incidence lemmas | Pournin Theorems 4,5 and Corollary 2; exact costs 2 and 5 | G, cyclic crossing/link laws; contiguous-block deletion invariance. |
| I. Explicit families and identities | Z,A,B,C defined by actual edge sets/deletions/flips/relabelings; valid triangulations; parity cases, links and small exceptions; simultaneous dihedral isomorphisms | B,G; source Figures 4–12, finite certificates for small sizes. No picture-defined opaque family or theorem fields for required identities. |
| J. Main recurrence | Theorems 6–11, including complementary-case normal form and B/C deletion costs | E–I. Preserve the ∀-over-geodesics force of the Θ upper bounds. |
| K. Finite lower seeds and induction | Necessary m=7,…,12 bounds, or the source's fuller m=3,…,12 development; exact 2m−10 lower bound for m≥13 | H–J and concrete small-family diagonal certificates. No brute-force diameter oracle needed. |
| L. Exact maximum for trees | All N-node shapes have distance≤2N−6 and explicit transported A_(N+2) endpoints attain it; derive the diameter equality for N≥11 | C,D,K plus the actual distance/maximum semantics from A. |

Stage A is now supplied by `Trees.Rotations.distance`, defined by minimizing lengths of **actual legal traces**, using connectivity for existence; a theorem-valued field “distance has the desired properties” is not a definition of the requested metric. A finite `max` over all same-size shapes is optional at first: the universal upper bound plus a concrete attaining pair is an equivalent, often cleaner, final interface. If a diameter definition is added, prove that equivalence rather than replacing the canonical statement with a weaker bound.

All tree results should preserve the existing carrier's universe generality where appropriate. The polygon lower-bound witnesses themselves are unlabelled finite shapes. To lift them to a fixed arbitrary inorder list, prove the shape/decoration equivalence; do not assume labels are distinct or introduce a linear-order requirement irrelevant to rotations. For an existential diameter over arbitrary labelled trees, require a nonempty label type or work explicitly with Unit; an empty label type has no positive-size trees.

## 11. Consequential examples and failure modes for future development

These are proposed checks with mathematically justified expected outcomes, **not executed Lean tests**:

- **Size threshold:** N=11 corresponds to m=13,d=10 and expected exact distance/diameter 16. N=10 corresponds to m=12,d=9, whose diameter is 15; the expression 2N−6 gives 14 and must not be asserted there. A_12 itself has distance 14, so a witness-only test misses the erroneous universal threshold.
- **Small family versus diameter:** A_9 distance 8 while the 9-gon diameter is 9; A_10 distance 10 versus diameter 11. The A-family is deliberately adequate for the large-size induction without being maximally distant at every small size.
- **Legal mixed traces:** a two-node right comb cannot perform a right rotation at its root, whereas the inverse-direction step is legal. A failed `Option` operation must not become a zero-cost or counted identity edge in the graph. A schedule's positions/edges are checked after previous steps, not only in the initial object.
- **Inorder restriction:** two labelled single-node trees with unequal labels have the same node count but cannot be connected by rotations. Conversely, repeated labels create no obstruction when the entire inorder lists agree. Shape diameter cannot be accidentally defined over disconnected arbitrary label assignments.
- **Fixed polygon labels:** reflect/rotate both endpoints together and preserve distance. Rotating only one endpoint can change the pair and its distance; quotienting each endpoint independently would break the desired graph correspondence.
- **Normalization:** an already present target diagonal is fixed; a single flip introducing it collapses under normalization; a flip in a disjoint region survives; crossing diagonals create spokes that may be boundary edges. A remove-then-reinsert detour of a common diagonal has at least two removable steps, not merely one.
- **Deletion:** an incident flip collapses after deleting the adjacent vertex; a nonincident flip survives once. Distinct old edges can merge, so mapping an edge list without deduplication gives the wrong cardinality. Deletion after a prior deletion uses the new clockwise successor, while designated family vertex identities remain original until relabelling.
- **Quantifiers:** Θ≥k requires existence of a geodesic with at least k incidents, and Θ≤k constrains all geodesics. Never infer a maximum bound from one observed shortest path. Theorem 8's lifting of every smaller geodesic is an explicit test of this distinction.
- **Family boundaries:** m=8/9/10 for A, q=7/8/9 for B/C, and q=12/13 for the B-deletion drawings change the comb/zigzag pattern. Test both parities and these exact boundaries before a generic formula is used in a theorem.
- **Finite lower-bound obstruction:** A_6 has three differing diagonals but source distance 4 because no first flip introduces a target diagonal. Q_11 has the reported analogous five-diagonal obstruction. Q_10 instead needs the separate target-introducing-first-flip/two-step analysis described above; its original no-first-target argument is disputed. A mere symmetric-difference count loses the extra unit needed in the finite B/C bases.
- **Offsets:** the B branch is 1+5 deleted vertices and 3+9 cost; the C branch is 1+4 deleted vertices and 3+7 cost. At m=13 the resulting A sizes can be 12,11,8,7; every needed induction seed must exist and use the right size variable.

## Remaining work

The explicit zigzag formula has the later ear-cutting paper argument below;
its primary-family identification and formal proof remain open. The finite
polygon model, normalization, deletion, family identities, finite seeds and
sharp upper/lower bounds still need actual formalization and review. The later
literal Q10 tables resolve the local finite obstruction without establishing
the disputed primary-family identification. Reuse the existing mixed-distance
foundation, then establish the concrete tree/flip correspondence. FDSA-5-92 and
all other remaining book obligations stay open.

## Concrete finite obstruction

Prepared 20 November 2026 for increment 083. This is mathematical preparation,
not a Lean qualification, source change, or acceptance receipt. CTB-24/FDSA-5-92
remains mandatory: for N internal nodes and N≥11, every two shapes have rotation
distance at most 2N−6, and a specified pair attains that value. The certificate/NP
work under FDSA-5-93 is separate.

### 1. What was actually inspected, and the remaining source boundary

The complete maintained paper
`docs/research/fdsa-rotation-diameter-preparation.md` and the complete FDSA-5-92 row
in `docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md`
were read in the historical source checkout. Their remaining obligations
are retained; this note replaces neither file.

Fresh primary reading used Lionel Pournin, *The diameter of associahedra*:

- <https://arxiv.org/pdf/1207.6296>, whose returned body identifies itself as
  arXiv:1207.6296v4, 28 March 2014, 28 pages.
- <https://ar5iv.labs.arxiv.org/html/1207.6296>, the conversion of that paper,
  especially §3.1–3.2 (family definitions) and §5, Proposition 7.
- Relevant manuscript locations: pp.11–12, Figure 4 and the A construction;
  pp.14–16, B/C construction and Figures 7–8; pp.22–23, Proposition 7 and
  Figure 12; pp.23–24, Theorems 12–13. DOI:
  <https://doi.org/10.1016/j.aim.2014.02.035>.

The Proposition 7 text says, using its variable n, “no flip can introduce an
edge of Q_n^+ into Q_n^-” when 10≤n≤11. The literal Q10 configurations below contradict this
sentence **if** their identification with the paper's diagram-defined family
is established. That identification is not newly authenticated here: PDF
screenshot calls returned text markers without inspectable image content;
versioned PDF/source requests were disabled. The fresh text establishes the
sentence and the deletion/relabel conventions, not a fresh visual reading of
Figures 4 or 12. Do not report a proved error in Pournin on this evidence alone.

No raw Pournin PDF was acquired or hashed. The maintained paper's historical
pin, 964,617 bytes / SHA256
`2f5a4ea8866e60b31a765549e48f3620dae34c0b75158cc9a1d53f9bbe1f295b`,
remains historical attribution. No fresh STT reading or whole-paper/whole-book
inspection is claimed. The lost independent Q10 memo was not recovered.

### 2. Explicit reconstructed objects and why they are usable mathematics

Here `ab` means the unordered edge `{a,b}` when both labels are single digits.
All polygons have the stated cyclic order, and all boundary edges are included
implicitly. Tables list only interior diagonals. Q10 is an **eight-vertex**
polygon after deletion, not a ten-vertex polygon.

The reconstruction uses the retained proposed Z formula: for an m-gon, its
m−3 interior diagonals, indexed by 0≤j≤m−4, are

\[
d_{2r}=\{2-r,4+r\},\qquad
d_{2r+1}=\{1-r,4+r\}\quad(\bmod m).
\]

For m=3 there are no diagonals and the polygon is already a triangle. For
m≥4 there is an elementary validity proof independent of a picture: successively
cut ears with labels `3,2,4,1,5,0,6,…` modulo m. At step 2r the removed block is
`[3−r,2+r]` and the next ear is `3+r`; its current neighbors are `2−r,4+r`.
At step 2r+1 the removed block is `[3−r,3+r]` and the next ear is `2−r`;
its current neighbors are `1−r,4+r`. Until the last cut at j=m−4 the neighbors
are distinct. These are exactly the displayed diagonals, and cutting ears
leaves a triangle. Thus the explicit formula defines a valid zigzag
triangulation. Matching its orientation/labels to the source's Figure 4 is
still a separate source-correspondence obligation.

To reproduce the finite data, use the maintained paper's construction with
original vertex identities retained until relabeling: A_m starts with
Z_(m+4); the minus side deletes 0,1,bar(0),bar(1) and keeps original 2 labeled
2; the plus side deletes 4,5,bar(4),bar(5) and sends original 2 to label 1.
Bars use the original m+4. Every deletion collapses toward the **current**
clockwise successor and deduplicates edges. B_q uses A_(q+1), the three actual
minus flips 25,24,26, then removes the common ear at 2; relabel keeping 3.
C_q changes B_q's 46 diagonal to 35. For Q9/Q10 delete 1,2; for Q11 delete
0,1,2; do not relabel Q afterward.

Inline finite set calculations reconstructed these data and enumerated flips
by their two incident triangles; no compiler, repository test, or acceptance
audit was run. The literal sets and exhaustive local tables below are the
retained evidence, not an opaque search result. Their internal validity is
also visible directly: every listed set has m−3 mutually noncrossing
diagonals in its stated cyclic order. Consequently the local results below
hold for these explicit objects whether or not the source-family mapping is
later confirmed. No alternate family is asserted to satisfy the global
Pournin recurrence without proof.

### 3. The replacement lemma: count missing target diagonals

Fix a target triangulation V and let

\[
M_V(T)=|I(V)\setminus I(T)|,
\]

where I is the interior-diagonal set. If a legal flip removes e and inserts f,
then e∈I(T), f∉I(T), and

\[
M_V(T')+\mathbf1_{f\in I(V)}
=M_V(T)+\mathbf1_{e\in I(V)}.
\]

This exact identity follows by separately removing e and inserting f. In
particular a step decreases M by at most one; if it inserts no target
diagonal, it does not decrease M at all. A path from U to V must decrease M
from r=M_V(U) to zero, so its length is at least r. If it has at least one
nondecreasing step, its length is at least r+1: sum the per-step inequalities,
using zero decrease at that step and decrease at most one elsewhere. This
argument allows a later removal/reintroduction of target edges; that behavior
only makes the estimate stronger.

**Two-prefix form.** Suppose r≥2, and every legal two-step prefix from U has
at least one step that inserts no target diagonal. Every U→V path already has
length at least r, hence has such a prefix, and therefore has length at least
r+1. A sufficient condition is that every target-introducing first move has a
successor from which no target-introducing move is possible. Uniqueness of the
first move is convenient finite evidence, not a necessary hypothesis.

This is a statement about **every legal path**. It needs neither a selected
geodesic, a maximum-incidence theorem, a target-first normalization, nor an
assumption that paths preserve common diagonals. Natural-number proofs can
use the displayed additive identity without truncated subtraction.

### 4. Q10: complete first and second flip tables

Use cyclic order `(0,3,4,5,6,7,8,9)`. The common target and two initial sets are:

| State | Interior diagonals |
| --- | --- |
| V | 39,48,49,58,68 |
| U_B | 07,36,37,46,79 |
| U_C | 07,35,36,37,79 |

For an independently checkable triangle certificate, U_B has triangles
`037,079,346,367,456,789`; U_C replaces `346,456` by `345,356`.
V has triangles `039,349,458,489,568,678`. In particular 07 is incident to
037 and 079, so the legal flip 07→39 introduces a target diagonal in both
variants. The no-first-target assertion is false for these literal objects.

Each row below gives one of **all five** first flips and **all five** second
flips available after that first flip. An asterisk marks insertion of a
target diagonal. This includes undo moves and all initially non-progressing
branches; no move is silently excluded as non-geodesic.

| Initial state | First flip | Every second flip from its result |
| --- | --- | --- |
| U_B | 07→39* | 36→47; 37→69; 39→07; 46→35; 79→38 |
| U_B | 36→47 | 07→39*; 37→04; 46→57; 47→36; 79→08 |
| U_B | 37→06 | 06→37; 07→69; 36→04; 46→35; 79→08 |
| U_B | 46→35 | 07→39*; 35→46; 36→57; 37→06; 79→08 |
| U_B | 79→08 | 07→38; 08→79; 36→47; 37→06; 46→35 |
| U_C | 07→39* | 35→46; 36→57; 37→69; 39→07; 79→38 |
| U_C | 35→46 | 07→39*; 36→47; 37→06; 46→35; 79→08 |
| U_C | 36→57 | 07→39*; 35→47; 37→05; 57→36; 79→08 |
| U_C | 37→06 | 06→37; 07→69; 35→46; 36→05; 79→08 |
| U_C | 79→08 | 07→38; 08→79; 35→46; 36→57; 37→06 |

These tables are obtained by taking the two third vertices adjacent to each
removed diagonal and joining them. For example, after 07→39 in U_B, diagonal
37 has triangles 367 and 379, hence flips to 69; diagonal 79 has triangles
379 and 789, hence flips to 38. Neither is in V. The number of rows/choices
is exhaustive because an eight-vertex triangulation has five flippable
interior diagonals.

Both initial sets have M=5. Their only target-introducing first flip is
07→39; every possible second move after it inserts a non-target edge. Thus
the two-prefix lemma proves **every U_B→V and U_C→V path has length at least
6**. For the undo second move M goes 5→4→5; for each other second move in
those two rows it goes 5→4→4. If the first move is unstarred, it already
uses the required nondecreasing step. No equality of the two distances, and
no exact distance beyond this lower bound, is claimed here.

### 5. Other small data needed by the same induction

These are additional independently reconstructed literal cases. They reduce
the finite prerequisites without changing the required final theorem.

#### A7, A8 and B8/C8

These polygons use consecutive cyclic labels 0 through m−1.

| Pair | Minus diagonals | Plus diagonals | Sufficient bound |
| --- | --- | --- | --- |
| A7 | 05,15,24,25 | 03,13,36,46 | ≥4 by four missing targets |
| A8 | 06,16,24,25,26 | 03,13,37,47,57 | ≥6 by five missing targets and the table below |
| B8 | 06,16,26,36,46 | 03,13,37,47,57 | ≥5 by five missing targets |
| C8 | 06,16,26,35,36 | 03,13,37,47,57 | ≥5 by five missing targets |

All A8 first flips are `06→17, 16→02, 24→35, 25→46, 26→15`; none inserts a
target. This gives the needed A8≥6 directly. It avoids a forced-incidence
lemma merely to obtain this weaker seed, and avoids proving its unnecessary
exact distance 7. For completeness A7's first flips are
`05→16, 15→02, 24→35, 25→14`; none inserts a target, so the stronger ≥5 also
holds for this literal pair. Only ≥4 enters the proposed induction.

#### Q9 and Q11

| Pair | Cyclic vertices | Minus diagonals | Plus diagonals |
| --- | --- | --- | --- |
| Q9, B variant | 0,3,4,5,6,7,8 | 07,36,37,46 | 38,48,58,68 |
| Q9, C variant | same | 07,35,36,37 | same |
| Q11, B variant | 3,4,5,6,7,8,9,10 | 36,37,38,46,{8,10} | 49,{4,10},59,69,79 |
| Q11, C variant | same | 35,36,37,38,{8,10} | same |

Q9 has four missing targets, giving ≥4. Q11 has five; its complete first-flip
table is:

| Variant | Every first flip |
| --- | --- |
| B | 36→47; 37→68; 38→{7,10}; 46→35; {8,10}→39 |
| C | 35→46; 36→57; 37→68; 38→{7,10}; {8,10}→39 |

None inserts a Q11 target. The one-stall lemma therefore gives ≥6 for both
literal Q11 pairs. Q11's first-move obstruction must not be copied to Q10.

### 6. Exact use in the still-open global lower-bound route

The finite potential results above are independent mathematics. Their use
as the paper's named A/B/C/Q seeds still requires the source-family mapping
and concrete deletion identities. Retain the maintained paper's proof of
the q9/q10 deletion loss 3 and q11 deletion loss 5 as **obligations**, not
assumed oracle fields. Once those identities and incidence proofs exist:

| q | Literal Q bound | Required deletion loss | Result for both B_q,C_q |
| --- | --- | --- | --- |
| 8 | Direct five-target count, no Q | 0 | ≥5 |
| 9 | ≥4 | 3 | ≥7 |
| 10 | ≥6, using the repaired two-prefix proof | 3 | ≥9 |
| 11 | ≥6 | 5 | ≥11 |

With A7≥4 and A8≥6, the actual Proposition 4 recurrence then gives the needed
A9,A10,A11,A12 lower bounds 8,10,12,14. The general four-offset recurrence
can start at m=13: its predecessor sizes are m−1,m−2,m−5,m−6, all at least
7, and its corresponding additions are 2,4,10,12. Each resulting lower
bound is 2m−10. Use a strong induction restricted to the defined family
range, not an induction hypothesis referring to A0,A1,A2.

This repairs a finite step of the existing A-family route; abandoning it
for the paper's D-family would not solve the problem. The necessary next
implementation components remain concrete finite cyclic triangulations,
legal flips, the actual source-correspondence/explicit-family identities,
path contraction and incidence bounds, normalization/ear lifting where
the global recurrence uses them, and that recurrence itself. None is
provided by these small tables.

For the final tree theorem retain the distinct quantities m=N+2 and d=N−1.
The universal fan upper bound and the rooted tree/flip distance equivalence
are still necessary, as is an explicit attaining pair. Reuse
`Applications/Trees/Rotations/Mixed.lean` and
`Applications/Trees/Rotations/Distance.lean` for actual legal traces and
attained distance; the primitive certificate work supplies no sharp
diameter theorem by itself. All existing qualification and publication
boundaries remain unchanged.

**Immediate bounded mathematical increment:** prove the missing-target
identity and its one-/two-prefix path lemmas for a concrete flip model, with
the above literal Q10 pair as both a positive lower-bound case and a negative
case for no-first-target. In parallel preparation, authenticate Figure 4's
orientation and Figure 12's labels against acquired primary bytes. If the
mapping differs, retain the valid literal lemmas and correct the family
correspondence; do not alter the expected flip data to fit a desired proof.

## Tree-diagonal bridge

20 November 2026. Read-only mathematical handoff; no new Lean proof or source
change is claimed. This builds on the complete
the preceding concrete finite-obstruction section, whose primary-source and
qualification boundaries remain. The Q10 figure/source-family identification
is unresolved; the literal objects below are independent of that identification.
CTB-24/FDSA-5-92, its global recurrences, sharp upper bound and attainer remain open.

### 1. Recommended reuse and actual current interfaces

Start with a finite diagonal **observation of the existing trees**, using the
existing rotations and trace interpreter. `Trees.Rotations.Shape N` can serve
as a representation of rooted triangulations. No new graph or tree datatype
is needed to prove the finite potential lower bounds. Calling it a
representation of *all* ordinary polygon triangulations additionally requires
the reconstruction theorem described below; an abbreviation alone does not
establish that correspondence.

The following complete owners were inspected in
the historical source checkout: `Applications/Trees/Rotations/Basic.lean`,
`Position.lean`, `Mixed.lean`, `Distance.lean`, and the supporting
`Applications/Trees/BasicObservations.lean`, `Observations.lean`, `Direction.lean`.
The relevant governing domain, architecture and formal-development guidance was
also read. Exact public interfaces used by this plan are:

| Owner / namespace | Existing interface and argument order |
| --- | --- |
| `Rotations/Basic.lean`, `Trees.Rotations` | `rotateRight? : BinaryTree α → Option (BinaryTree α)`; `.node b (.node a A B) C ↦ some (.node a A (.node b B C))`. `rotateLeft?` is the inverse pattern; other shapes return `none`. |
| Same | `rotateRight?_eq_some_iff (t s)` exposes exactly that decomposition; `rotateRight?_numNodes (h : rotateRight? t = some s)` proves `s.numNodes = t.numNodes`. Corresponding left laws and both undo laws exist. |
| `Rotations/Position.lean` | `applyAt? (f : BinaryTree α → Option (BinaryTree α)) (p : List Branch) (t)`; `[]` calls f, and a nonempty path through nil fails. `applyAt?_inorder f preserve p run` lifts callback preservation. |
| `Direction.lean` | `Search.SharedTree.Branch.left/right` are path branches. These differ from `RotationDirection.left/right`. |
| `Rotations/Mixed.lean` | `RotationMove` has fields `direction : RotationDirection`, `position : List Branch`. `applyMove? move t := applyAt? move.direction.apply? move.position t`. |
| Same | `applyMoves? moves t` is sequential `foldlM`; `applyMoves?_cons move moves t` exposes its bind. `applyMove?_inorder move run`, `applyMoves?_numNodes moves run`, append and undo laws are available. |
| `Rotations/Distance.lean` | `Shape N := {t : BinaryTree Unit // t.numNodes = N}`. `Shape.distance_spec s t` gives an actual successful move list whose length equals `Shape.distance s t`. `Shape.distance_le_length s t run` gives an **upper**, not lower, bound. |

The proposed `spans`/`diagonals` names below are mathematical notation, not
existing declarations. Constructor order is `.node label left right`.

### 2. Concrete observation, counts, noncrossing and recovery

Write |t| for `t.numNodes`. Use ordered pairs of naturals `(a,b)` with a<b;
endpoint bounds can later provide a `Fin (N+2)` view without complicating
recursive offset arithmetic. Define H(k,t), all nonempty occurrence spans,
by the structural equations

\[
\begin{aligned}
H(k,\mathrm{nil})&=\varnothing,\\
H(k,\mathrm{node}(a,l,r))
 &=\{(k,k+|l|+|r|+2)\}\cup H(k,l)
      \cup H(k+|l|+1,r).
\end{aligned}
\]

Define D(k,nil)=∅ and
`D(k,node a l r) = H(k,l) ∪ H(k+|l|+1,r)`.
Thus D excludes the selected global root span, and `diagonals(t)=D(0,t)`.
For |t|=N>0 the root span is `(0,N+1)`, the distinguished boundary edge of
the polygon with vertices 0,…,N+1. Each proper nonempty subtree with offset k
and n nodes gives `(k,k+n+1)`. Nil occurrences would give consecutive boundary
edges; they contribute nothing to H or D.

**Occurrence identity is essential.** `Trees.subtrees t` is a set of subtree
*values*, not positions, and is unsuitable for this count. For
`S=node () nil nil`, the tree `node () S S` has distinct diagonals `(0,2)`
and `(2,4)`, although both children are equal to S. Structural recursion with
offsets retains both occurrences without needing labels to be distinct.

The following proofs follow directly by structural induction, but must still
be implemented:

1. Every H(k,t) edge has endpoints in `[k,k+|t|+1]` and length at least 2.
   An occurrence strictly below the root has strictly smaller span length.
2. At a node put q=k+|l|+1. Left edges lie in `[k,q]`; right edges lie in
   `[q,k+|t|+1]`. Their interiors are disjoint, so the two finite sets are
   disjoint; neither contains the root span. This proves `card H(k,t)=|t|`
   and `card D(k,t)=|t|−1` (natural subtraction, including nil).
3. Two occurrence intervals are nested, or have disjoint interiors: at their
   first divergent branch they occupy those two child regions. Hence no pair
   has alternating endpoints `a<c<b<d` or `c<a<d<b`. This is exactly the
   convex cyclic noncrossing test for sorted endpoints.
4. For N≥1, D(0,t) contains no polygon boundary edge: each has length≥2,
   and none is `(0,N+1)`. Adding the N+1 consecutive boundary edges and the
   closing root edge gives `2N+1=2(N+2)−3` full edges. The N−1 diagonals form
   an ordinary triangulation; this last conclusion needs either the standard
   maximal-noncrossing cardinality proof or the recursive triangle decomposition.

The recursive decomposition is particularly direct. The root triangle is
`(k,q,k+|t|+1)`, and the left/right subtrees triangulate its two remaining
regions. A nil child is a boundary edge, not a zero-area triangle. Induction
gives N triangles, including the selected root triangle, and supplies the
geometric interpretation without a theorem-valued triangulation oracle.

**Injectivity on a fixed size.** For Unit trees with the same N, equality of
D determines the tree. Add the known polygon boundary edges. For N≥1 the
root split q is the unique interior vertex such that both `(0,q)` and
`(q,N+1)` belong to this full edge set. Existence follows from the root
decomposition. If q<q' both worked, `(0,q')` and `(q,N+1)` would cross, proving
uniqueness. It determines `|l|=q−1`, `|r|=N−q`. Restrict the common diagonal
set to the two closed regions, remove the child root span when nonempty, and
apply induction to recover both children. Offset translation gives the same
argument for arbitrary k. Size zero has only nil.

The hypotheses matter: nil and a singleton both have empty D, so D alone
is not injective across arbitrary sizes; arbitrary node labels are also
forgotten. Either use Unit/shape recovery, or additionally recover labels from
a common inorder sequence. No injectivity for arbitrary differently labelled
trees is being claimed.

**All-polygon correspondence still owed.** Given any maximal noncrossing
triangulation with root edge `(0,N+1)`, prove existence/uniqueness of its
incident root triangle, split along that triangle, and recurse to construct
the Unit tree. Prove both reconstruction directions. This is the useful
surjectivity/recovery contract if the Pournin operations are first described
on ordinary triangulations. It is not needed merely to interpret the three
explicit tree values in §5 or prove their trace lower bounds.

### 3. A legal rotation changes exactly one diagonal

Consider an actual right rotation at offset k:

`node b (node a A B) C  →  node a A (node b B C)`.

Put u=|A|, v=|B|, w=|C| and

\[
x_0=k,\quad x_1=k+u+1,\quad x_2=k+u+v+2,\quad
x_3=k+u+v+w+3.
\]

Then x0<x1<x2<x3 even if A, B or C is nil. The changed edge is
`e=(x0,x2)` and its replacement is `f=(x1,x3)`. In both trees A is at x0,
B at x1, C at x2; their spans are identical. The selected subtree's outer
span `(x0,x3)` is also identical. Expanding H/D therefore proves

\[
D(k,t')=(D(k,t)\setminus\{e\})\cup\{f\},
\quad e\in D(k,t),\quad f\notin D(k,t).
\]

The same erase/insert identity holds for H, retaining the outer span. All
other spans lie in one of the A/B/C regions; none is e or f. Alternatively,
f's absence follows from crossing e and the established noncrossing law.
The two old triangles are `(x0,x1,x2)` and `(x0,x2,x3)`; the two new ones
are `(x0,x1,x3)` and `(x1,x2,x3)`. This is an actual quadrilateral flip,
including the cases with boundary sides from nil children. Left rotation
reverses the calculation.

For a successful `applyAt?` at any position p, compute the offset by leaving
it unchanged on a left branch and adding `|left|+1` on a right branch.
Induct on p using the exact `applyAt?` equations. Root rotations preserve
subtree size, so ancestor outer spans and all right-sibling offsets remain
unchanged, including when the selected child is the left child. The H identity
handles a selected proper subtree whose own outer span belongs to the global D;
the D identity handles p=`[]`. Thus every successful `applyMove? move t=some t'`
has an actual pair e,f with the same global erase/insert identity and e≠f.
This law is to be derived from the definitions, not supplied as a field.

There is also a useful converse within the tree representation. Every D edge
comes from a unique nonempty proper occurrence: ancestors have different span
lengths; incomparable occurrences have disjoint interiors. It has a unique
parent path. If it is a left child, a right rotation at that parent removes
it; if a right child, a left rotation does. Consequently the N−1 diagonals
are in bijection with the successful directed moves on an N-node tree (N>0).
This also proves exhaustiveness of finite legal-move tables. A geometrically
specified flip of that edge matches this move after proving uniqueness of
the two incident triangles/opposite quadrilateral diagonal. Do not replace
that proof by assuming any arbitrary finite-set exchange is a legal rotation.

### 4. Transport the potential through the existing interpreter and distance

For a fixed target v define `M_v(t)=card (D(0,v) \ D(0,t))`. The concrete
one-diagonal law from §3 gives the exact identity from the 083 note:

`M_v(t') + [f ∈ D(0,v)] = M_v(t) + [e ∈ D(0,v)]`.

Here brackets are 0/1 indicators. Each successful move drops M by at most
one. A move inserting no target edge drops it by zero or increases it.
Induct on `moves`, expanding **the actual** `applyMoves?_cons` bind, to obtain
`M_v(t) ≤ moves.length + M_v(t')` for any successful run to t'. At the
target M is zero. This proof neither defines a replacement interpreter nor
counts failures as identity moves.

For the two-prefix improvement, prove the concrete local property for every
two successful moves from t: `M_v(t) ≤ M_v(t₂)+1`. If M_v(t)≥2, the ordinary
bound rules out target-reaching traces of length 0 or 1. Decompose an arbitrary
remaining trace into its first two moves and tail. The local property plus
the tail bound yields `M_v(t)+1 ≤ moves.length`. The stronger 083 condition
that one of the first two flips inserts no target edge implies that property.

To conclude a lower bound on **existing** `Shape.distance s v`, obtain its
attaining successful trace from `Shape.distance_spec s v` and apply the
universal trace lower bound. `Shape.distance_le_length` cannot be used in
the opposite direction. No generic polygon distance or shortest-path oracle
is required. Full reconstruction/injectivity is also unnecessary for this
particular implication: the endpoint is already the actual target tree.

### 5. Explicit six-node trees for the Q10 literal objects

Normalize the 083 cyclic labels by the order-preserving map

| Old label | 0 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| New label | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |

Root edge 09 becomes `(0,7)`. Write `E=nil`, `n(l,r)=BinaryTree.node () l r`,
`S=n(E,E)`, `P=n(E,S)`, `Q=n(S,E)`. Define the concrete values

\[
\begin{aligned}
b&=n(n(E,n(P,E)),S),\\
c&=n(n(E,n(Q,E)),S),\\
v&=n(E,n(E,n(n(E,P),E))).
\end{aligned}
\]

S has one node; P and Q have two; each of b,c,v has six. These values were
reconstructed by the root-triangle splits, then checked by direct finite
arithmetic on trees and their legal root-rotation equations. This was an
inline mathematical calculation, not a Lean compilation/test or acceptance.

The complete nonempty-occurrence span lists provide a short reconstruction
certificate. Here L/R mean path branches, and ε is the empty path:

| Tree | Path: span; root-triangle split vertex |
| --- | --- |
| b | ε:(0,7);5 — L:(0,5);1 — LR:(1,5);4 — LRL:(1,4);2 — LRLR:(2,4);3 — R:(5,7);6 |
| c | ε:(0,7);5 — L:(0,5);1 — LR:(1,5);4 — LRL:(1,4);3 — LRLL:(1,3);2 — R:(5,7);6 |
| v | ε:(0,7);1 — R:(1,7);2 — RR:(2,7);6 — RRL:(2,6);3 — RRLR:(3,6);4 — RRLRR:(4,6);5 |

Removing the ε entry gives:

| Tree | Normalized diagonal set | In old labels |
| --- | --- | --- |
| b | (0,5),(1,4),(1,5),(2,4),(5,7) | 07,36,37,46,79 |
| c | (0,5),(1,3),(1,4),(1,5),(5,7) | 07,35,36,37,79 |
| v | (1,7),(2,6),(2,7),(3,6),(4,6) | 39,48,49,58,68 |

These are exactly the **literal** Q10 sets retained in 083. This establishes
their concrete tree realization, not their identification with Pournin's
figure-defined family. Six is the number of tree nodes here; Q10's subscript
refers to its auxiliary source construction, not a ten-node tree.

The following are all successful first moves. Direction names are the actual
`RotationDirection` constructors; paths use `Branch` constructors. Exchanges
are shown in old labels so they can be compared directly with 083.

| Tree | Position | Rotation | Edge exchange | M_v afterward |
| --- | --- | --- | --- | --- |
| b | ε | right | 07→39 | 4 |
| b | ε | left | 79→08 | 5 |
| b | L | left | 37→06 | 5 |
| b | LR | right | 36→47 | 5 |
| b | LRL | left | 46→35 | 5 |
| c | ε | right | 07→39 | 4 |
| c | ε | left | 79→08 | 5 |
| c | L | left | 37→06 | 5 |
| c | LR | right | 36→57 | 5 |
| c | LRL | right | 35→46 | 5 |

The unique target-introducing first move is `⟨.right, []⟩`. Its actual results
are `b'=n(E,n(n(P,E),S))` and `c'=n(E,n(n(Q,E),S))`.
All successful next moves are:

| Tree | Position | Rotation | Edge exchange | M_v afterward |
| --- | --- | --- | --- | --- |
| b' | ε | left | 39→07 | 5 |
| b' | R | right | 37→69 | 4 |
| b' | R | left | 79→38 | 4 |
| b' | RL | right | 36→47 | 4 |
| b' | RLL | left | 46→35 | 4 |
| c' | ε | left | 39→07 | 5 |
| c' | R | right | 37→69 | 4 |
| c' | R | left | 79→38 | 4 |
| c' | RL | right | 36→57 | 4 |
| c' | RLL | right | 35→46 | 4 |

No second move inserts a target edge. Every other first move already leaves
M at five. Thus the proposed trace theorem yields
`6 ≤ Shape.distance bShape vShape` and `6 ≤ Shape.distance cShape vShape`
after constructing their size-six witnesses and connecting these tables to
the public definitions. These are paper derivations, not existing Lean
theorems. They assert lower bounds only, not exact distances or the global
sharp-diameter theorem.

For a formal exhaustive table, prove that any successful `applyMove?` on
each displayed tree occurs among the five listed moves. Structural case
analysis of positions suffices: positions selecting nil and descent through nil fail,
and at each nonempty position only the directions with a nonempty selected
child succeed. The five-diagonal/unique-occurrence theorem offers a reusable
alternative proof of exhaustiveness. Neither method assumes shortestness.

### 6. Bounded next development and retained obligations

The first coherent implementation can consist of H/D, their offset and
disjointness laws, the actual-root and `applyAt?` one-diagonal laws, the
trace-potential inequalities, and these three explicit Unit-tree cases. State
and prove the local conditions needed by the two-prefix lemma; do not pass a
whole desired distance bound, arbitrary cost oracle or assumed flip-correctness
record. Keep these pure observations independent of the measured certificate
and codec writers' scope.

The observation/recovery programme can then add fixed-size injectivity,
rooted-triangulation reconstruction and adjacency reflection when the geometric
consumers need them. Define flips through the unique proper occurrence and
the existing move operation where practical. A separate mathematical
triangulation presentation can still be valuable for deletion, fan routing
and normalization, but connect it by proved recovery and step laws rather
than maintaining unrelated distance semantics.

All global obligations remain: authenticate the primary family's figures and
conventions; construct the A/B/C families and deletion/normalization/ear maps;
prove the exact recurrence and finite-seed correspondence; prove the universal
fan upper bound and construct the attaining A_(N+2) pair for every N≥11.
Forward tree-to-diagonal preservation alone does not give polygon-path lifting,
all-triangulation surjectivity, a sharp upper bound, or the attaining family.
No qualification, publication, source edits or gate changes follow from this
note.
