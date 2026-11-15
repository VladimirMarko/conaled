# Chapter 13: Region Quadtrees — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-013`.

**State: queued; source preparation only.** This original inventory covers
printed pp. 161–175, with p. 176 blank, in the pinned July 27, 2026 book.
It does not activate the chapter, implement Lean, run a build, accept an
obligation or initiate a review loop. Every row still needs a checked
implementation or exact reuse witness and the applicable acceptance gates.

## Evidence and provenance

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 13 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. PDF pages 167–182. |
| Primary entry | <https://isa-afp.org/entries/Region_Quadtrees.html>, attributed to Tobias Nipkow, entry dated January 26, 2024, BSD license. The mutable entry/browser URLs are discovery links, not source pins. |
| Reproducible support snapshot | <https://isa-afp.org/release/afp-Region_Quadtrees-2026-10-26.tar.gz>, 20,141 bytes; SHA-256 `e428e079cad53676eb4a84cc3cd42efd8460d70475dc304a5f8bb41701c8e28f`. This support snapshot postdates the book; its relevant statements were compared with the manuscript. |
| `Quad_Base.thy` | Archive path `Region_Quadtrees/Quad_Base.thy`, 427 bytes; SHA-256 `6e1f30b2cf0b421b31fd0b04b57354e81c0e2d520f85dc73ce6477fa4a8d4e2f`. Shared four-child carrier and height. |
| `Quad_Tree.thy` | Archive path `Region_Quadtrees/Quad_Tree.thy`, 25,894 bytes; SHA-256 `ae67ef2c9ca555db8fab23e9b68e8f5a9303141544145415d6e52ad7f685e4e3`. Direct chapter/section link: <https://isa-afp.org/browser_info/current/AFP/Region_Quadtrees/Quad_Tree.html>. |
| `Quad_Matrix.thy` | Archive path `Region_Quadtrees/Quad_Matrix.thy`, 11,490 bytes; SHA-256 `1afd54b7bf7b7f65291ab70d7cf796c4922136809f21456965410c47d9d5f56f`. Direct §13.2 link: <https://isa-afp.org/browser_info/current/AFP/Region_Quadtrees/Quad_Matrix.html>. |
| `KD_Region_Tree.thy` | Archive path `Region_Quadtrees/KD_Region_Tree.thy`, 14,106 bytes; SHA-256 `27f9c79a8683ebdb3e55e843ec22498ea6d9745e96b55f5adb02c106ed943223`. Direct §13.3 link: <https://isa-afp.org/browser_info/current/AFP/Region_Quadtrees/KD_Region_Tree.html>. |
| Other archived developments | `KD_Region_Tree2.thy`, SHA-256 `14850e186a727775b6d3c970582408ce353dedbf973e5dc13df6ae71ff1086e3`, and `KD_Region_Nested.thy`, SHA-256 `f54976c8f244b92e7c748f848c92357d3a74e5d6b2e95dad028617de806dfba2`, are separately named alternatives. They are not substituted for the chapter's directly linked binary-split development and were not audited here. |
| License | The official AFP entry identifies the BSD license; shared `book-source/AFP-LICENSE` contains BSD-3-Clause terms. Retain the relevant notices for later translated source. |
| Lean reuse | Inspected conaled Chapter 1 candidate baseline `1aabd512284fe86254278ac631eda061d311050b`, whose relevant pre-existing APIs originate in checkout `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

All four directly relevant theories were read. A scoped scan found no
`sorry`, `oops`, `axiomatization` or `admit` token in them; this is not an
Isabelle rebuild or a proof audit. The diagram pages 161, 162, 165, 169 and
172 and the critical direction equations on p. 174 were rendered and visually
inspected. Full theories, page renders and manuscript extracts remain reading
inputs outside the deliverable; this original note and its pins are durable.

There are two exercises, 13.1 and 13.2. The source supplies union and difference
for 13.1. The generic function-to-image-quadtree exercise remains an explicit
Lean obligation; the real-matrix theory's `qtr` helper has a different semantic
context and no inspected theorem closing that exercise.

## Conventions, domains and precise reuse

Write `L a` and `Q t0 t1 t2 t3` for the source quadtree constructors, `h` for
height, and `d=2^n` at a recursive step. These abbreviations are for the
inventory, not proposed public Lean notation. Ordinary image compression,
diagonal-matrix compression, and binary region-tree compression are distinct
predicates and smart constructors. Their common printed names do not make
their semantics interchangeable.

The source's omitted zero-resolution/nonleaf cases are underspecified HOL
terms. Follow `fdsa-control/DECISIONS.md`: give a valid-resolution interface or
an explicit optional extension and prove its success/domain bridge. Do not add
`Inhabited α` to obtain a fallback pixel. `get` requires no payload equality;
an executable equality-testing smart constructor requires `DecidableEq α` or
an equivalent lawful comparison capability. Structural validity and observation
laws should not acquire that capability unless their operation uses it.

| Current API | Exact use and remaining gap |
|---|---|
| `Bracketing.Tree α`, `Tree.leaf`, `Tree.fork`, in `Applications/Bracketing/Basic.lean` | Exact leaf-labelled full binary carrier for §13.3's `Box`/`Split`, at arbitrary payload universe. Reuse it instead of introducing another binary tree. `fringeSpec`, leaf-count `size` and `forkCount` are existing observations; neither count is the chapter's height. |
| `Bracketing.Tree.fold`, `fold_fusion`, `fold_pair`, `fold_identity`, in `Bracketing/Interpretation.lean` | Existing structural interpretation interface. Height and other ordinary binary-tree observations fit it; path-dependent updates and resolution-dependent lookup need their own domain algorithms, not a stronger universal fold claim. |
| `Huffman.height`, `height_lt_size`, in `Applications/Huffman/Basic.lean` | Existing height on the same `Bracketing.Tree`, leaf zero and fork `1+max`. If dependency direction makes the Huffman import undesirable, move/share this existing observation while retaining its clients rather than create an unrelated duplicate height API. |
| Mathlib `BinaryTree α` | Not the §13.3 carrier: its empty leaves contain no values and its internal nodes carry payloads. It remains the right carrier for earlier ordinary binary-tree chapters. |
| Four-child carrier | No existing region-quadtree carrier or algorithms were found in the scoped conaled/Mathlib/Batteries search. A small domain carrier is a real gap. Encoding each `Q` as two binary levels requires a shape bridge, and binary compression can collapse an intermediate rectangle that ordinary quadtree compression cannot; it is not definitionally the same representation. |
| `List.zipWith`, `replicate`, `map`, `take`, `drop`, `getElem?`/proof-domain `getElem` | Exact list operations needed by `Qmx`, `decomp` and list-matrix indexing. Source `map2` truncates at the shorter input, exactly as `zipWith`; do not silently pad. Existing `length_take`, `length_drop`, `getElem_map`, `getElem_replicate` support the shape proofs. |
| `List.ofFn`, `List.getElem_ofFn`, `List.ofFn_const` | Finite function/list matrix bridge and a possible Exercise 13.2 construction. No default value is needed for valid finite coordinates. A function matrix and an arbitrary ragged list matrix remain different input domains. |
| Mathlib `Matrix m n R` | Existing functional matrix carrier. `Matrix (Fin (2^n)) (Fin (2^n)) R` gives the finite observation; an explicit zero extension connects it to the source's `Nat → Nat → R`. Preserve the all-natural-index equality where the source states it. |
| `Matrix.diagonal`, `diagonal_apply`, `diagonal_zero`, `diagonal_add`, `diagonal_mul_diagonal` | Exact diagonal mathematics after the finite-coordinate/zero-extension bridge. `diagonal` needs `Zero R` and decidable equality of the index; `diagonal_add` needs only `AddZeroClass R`. |
| `Matrix.fromBlocks`, `fromBlocks_add`, `fromBlocks_multiply`, in `Mathlib/Data/Matrix/Block.lean` | Existing block identities; the multiplication name is `fromBlocks_multiply`. Its assumptions are finite inner index types and `NonUnitalNonAssocSemiring R`, not an ordered field. `finSumFinEquiv` and its left/right equations identify two half-index blocks with a doubled finite index. |
| `Matrix.mul_apply`, `Finset.sum_fin_eq_sum_range` | Connect matrix multiplication's finite inner sum with the source sum over `0≤k<2^n`. `Matrix.mul_apply` itself requires `Mul R`, `AddCommMonoid R`, and finite inner index. These value identities are not execution-cost theorems. |
| `MatrixBackend.representation`, `additionSquare`, `compositionSquare`, in `Applications/Linear/Matrix.lean` | Existing `Squares` integration for a finite matrix representation and its linear-map observation. This interface uses `CommSemiring R`; the quadtree algorithm's algebraic core need not inherit that stronger assumption. |
| `StructuredLinear.denseMatrix`, `diagonalMatrix`, `denseEntries_correct`, `diagonalEntries_correct` | Connected existing dense/diagonal clients after a representation bridge. Their sparse/vector execution algorithms and measured costs do not describe quadtree execution. |

For matrix algorithms, a semiring with decidable scalar equality is already a
substantial generalization of the source's reals; most individual statements
need still weaker assumptions shown above. Real equality is not an executable
decision procedure. A classical real specialization may be mathematical and
noncomputable, while a rational or natural scalar specialization supplies a
checked executable client. Do not claim machine execution on arbitrary exact
reals merely because HOL's specification tests equality.

## 13.1 Basic image quadtrees: pp. 161–164

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-001 | Carrier `L : α → QTree α`, `Q : QTree α → QTree α → QTree α → QTree α → QTree α`; images have side `2^n`, with resolution `n`. | New four-child domain carrier; retain arbitrary payload universe and no arbitrary empty-image constructor. |
| C13-002 | Quadrant convention (13.1): in Cartesian coordinates `t0` is lower left, `t1` upper left, `t2` lower right, `t3` upper right; Figure 13.1 uses this order. | Checked coordinate clients must fix this convention. The matrix row/column convention below changes the visual layout while retaining argument order. |
| C13-003 | `h(L a)=0`; `h(Q t0 t1 t2 t3)=max(h t0,h t1,h t2,h t3)+1`. | `Quad_Base.height_qtree`. A nested natural maximum avoids a partial finite-set maximum. |
| C13-004 | Image `compressed` holds for leaves and for a `Q` exactly when all four children are compressed and are not four equal leaves. | `Quad_Tree.compressed`; a proposition needs no decidable equality. Distinguish structural normal form from semantic equality at one coordinate. |
| C13-005 | Image `Qc` replaces four leaf children by their first leaf precisely when all four labels agree; otherwise returns `Q`, including every mixed/nonleaf case. | `Quad_Tree.Qc`; executable equality capability belongs here. The catch-all has priority after the all-leaf clause. |
| C13-006 | Four compressed children imply `compressed(Qc t0 t1 t2 t3)`. | `compressed_Qc`. The constructor does not recursively normalize arbitrary uncompressed children. |
| C13-007 | Valid resolution is `h t≤n`; one leaf represents any resolution. The mixed four-leaf example cannot represent the 1×1 image but fits resolution 1. | Preserve the pair invariant independently of compression. It guarantees all lookup paths are defined; it is not asserted to be the maximal domain of every individual raw lookup. |
| C13-008 | `select x y a b c d` returns respectively `a,b,c,d` for `(true,true)`, `(true,false)`, `(false,true)`, `(false,false)`. | Source `select_def`; a small product/Boolean case split, with no payload capability. |
| C13-009 | Image `get` returns a leaf's label for all coordinates; on `Q` at resolution `n+1`, select using `i<2^n,j<2^n`, then recurse at `n` with each coordinate reduced modulo `2^n`. | `Quad_Tree.get`; `get 0 (Q …)` lacks a specified equation. Preserve source behavior for arbitrary natural coordinates on valid trees; no whole-image periodicity is implied. |
| C13-010 | `sq n` consists exactly of pairs whose coordinates are both `<2^n`. | Reuse products of `Set.Iio` or bounded `Fin` coordinates through an explicit equivalence. Zero resolution still contains the single coordinate `(0,0)`. |
| C13-011 | At zero resolution, `put i j a 0 (L b)=L a`. | Source `put` base; `Q` at zero resolution is outside the valid-resolution domain. |
| C13-012 | Successor `put` splits a leaf into four copies or takes the four existing children, then modifies exactly the selected child using residual coordinates and one smaller resolution. | Preserve source branch/argument order and reassembly via image `Qc`. This is an actual update algorithm, not function extensionality alone. |
| C13-013 | `modify f x y (t0,t1,t2,t3)` applies `f` only in the selected slot and rebuilds with `Qc`; the other three children are retained. | Source `modify`; four Boolean cases. No traversal of unchanged children. |
| C13-014 | If `h t≤n` and both updated and queried coordinates lie in `sq n`, lookup after `put` is `a` exactly at the updated coordinate and otherwise equals old lookup. | `get_put`. Both coordinate bounds matter for distinguishing points after half-range reduction. |
| C13-015 | `h t≤n → h(put i j a n t)≤n`. | `height_put`; no coordinate bound is required by this source theorem. |
| C13-016 | `h t≤n ∧ compressed t → compressed(put i j a n t)`. | `compressed_put`; again no coordinate bound. |
| C13-017 | Boolean trees represent the subset of `sq n` where lookup is true; Boolean `put` implements insertion or deletion of one valid point. | `points_put`, `get_points`, `points_subset` supply support. A set observation bridge must retain bounds; it must not identify duplicate-free set semantics with matrix payload semantics. |

## 13.1.2 Boolean operations and Exercise 13.1: pp. 164–165

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-018 | `inter(L b,t)` and `inter(t,L b)` return `t` for true and `L false` otherwise; two `Q` inputs recurse on corresponding children and reassemble with image `Qc`. | `Quad_Tree.inter`. Preserve the short-circuit leaf cases. |
| C13-019 | Valid resolutions for both inputs imply `get n (inter s t) i j = get n s i j ∧ get n t i j`. | `get_inter`; no coordinate restriction appears. |
| C13-020 | `h(inter s t)≤max(h s,h t)`. | `height_inter`; unconditional on compression or resolution. |
| C13-021 | Compressed inputs give compressed intersection. | `compressed_inter`. |
| C13-022 | Exercise 13.1, union algorithm: true leaf absorbs, false leaf returns the other operand, and the two-node branch recurses quadrantwise with `Qc`. | Direct support `union`; no new set carrier is needed. |
| C13-023 | Valid-resolution union agrees with pointwise disjunction and with union of the bounded point sets. | `get_union`, `points_union`; the lookup theorem is stronger than only bounded-coordinate equality. |
| C13-024 | Union does not exceed the maximum input height and preserves compression. | `height_union`, `compressed_union`; retain both conclusions. |
| C13-025 | Exercise 13.1, difference: a false left leaf gives false; a true left leaf complements the right tree; a true right leaf gives false and a false right leaf returns the left tree; two nodes recurse quadrantwise. | `diff`, with `negate` mapping Boolean leaves and retaining the ordinary `Q` constructor. Its complement helper is part of this concrete exercise solution. |
| C13-026 | Valid-resolution difference represents bounded set difference, or pointwise `get s ∧ ¬get t`; complement represents `sq n` minus the old set. | `points_diff`, `points_negate`; a direct all-coordinate `get_diff` theorem is not present in this theory and needs proof if exposed. |
| C13-027 | Difference preserves compression and fits the maximum input height; complement preserves height and compression. | `compressed_diff`, `compressed_negate` support normal form. The inspected theory does not name height lemmas for difference/complement; prove them from their actual recurrences. |
| C13-028 | The prose also identifies xor as another quadrantwise Boolean operation. | No xor operation is present in the inspected theory. A verified Boolean-combination specialization with xor leaf behavior covers the claim; avoid suggesting it is already a source-proved algorithm. There is no requested catalogue of all possible Boolean functions. |

## 13.1.3 Subimages: pp. 165–166, Figure 13.2

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-029 | `qf q f i j d = q (f i j) (f i (j+d)) (f (i+d) j) (f (i+d) (j+d))`. | Exact four offsets; generic function application requires no new framework. |
| C13-030 | `get_sq` on a leaf returns that leaf; requested resolution zero returns the leaf containing `get n t i j`. | Source `get_sq` first two priority-ordered clauses; lookup domain must remain explicit. |
| C13-031 | At source resolution `n+1` and requested resolution `m+1`, if both residual coordinate plus `2^(m+1)` fit within `2^n`, descend into the selected quadrant, retaining requested resolution `m+1`. | Exact “fits one quadrant” test, with non-strict `≤`. Equality at the boundary is accepted. |
| C13-032 | Otherwise run four `get_sq` calls on the original full tree at requested resolution `m`, with offsets supplied by `qf … (2^m)`, and reassemble with `Qc`. | The four calls need not correspond to four different original quadrants. Replacing their source tree by its four children is incorrect. |
| C13-033 | Termination decreases source resolution in the contained case and requested resolution in the other case. | A lexicographic pair or sum of these natural parameters decreases; include all branch domains. Structural recursion solely on the tree would not cover the second branch. |
| C13-034 | If `h t≤n`, the entire requested square fits (`i+2^m≤2^n`, `j+2^m≤2^n`), and `i',j'<2^m`, then extracted lookup equals source lookup at `(i+i',j+j')`. | `get_get_sq`; all five premises are retained. In particular a corner in bounds alone is insufficient. |
| C13-035 | `h t≤n ∧ compressed t → compressed(get_sq n t m i j)`, without a containment premise. | `compressed_get_sq`. The weaker semantic domain should not be imposed on this structural theorem. |
| C13-036 | The resulting tree fits the requested resolution whenever `m≤n`; source support proves `h(get_sq …)≤m`. | `height_get_sq`, whose statement does not require `h t≤n`; for a proof-domain Lean operation, advertise the source theorem on that operation's explicit domain. Containment implies `m≤n`. |
| C13-037 | Figure 13.2 illustrates a contained square crossing a quadrant boundary; the displayed 8×8 image admits the 4×4 square starting at `(1,1)`. | Useful client `(n,m,i,j)=(3,2,1,1)` exercises the full-tree subdivision branch. Also check a boundary-aligned contained square and a single pixel. |

## 13.1.4 Conversions and Exercise 13.2: pp. 166–168

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-038 | List matrix carrier is `List (List α)`; `sq_mx n mx` means exactly `2^n` rows and exactly `2^n` entries in every row. | Reuse standard lists; record shape as a separate predicate/subtype. Ragged/empty matrices are outside this positive square domain. |
| C13-039 | Source `map2` applies its function pairwise up to the smaller length. | Exact standard `List.zipWith`; preserve truncation even when proving later equal-shape clients. |
| C13-040 | `Qmx a b c d = zipWith (++) a b ++ zipWith (++) c d`. | Standard operations; shape hypotheses supply correct rectangular concatenation. |
| C13-041 | `mx_of n (L x)` is a `2^n`-by-`2^n` replication of `x`; the successor node case converts four children at `n` and applies `Qmx`. | `mx_of`; the image leaf is a constant block, not a diagonal. Zero-resolution nonleaf is underspecified. |
| C13-042 | Example: `mx_of 1 (Q (L 0) (L 1) (L 2) (L 3)) = [[0,1],[2,3]]`; indices `(0,1)` and `(1,0)` return 1 and 2. | Check the exact example. It connects Cartesian image order to row-major matrix display and catches transposition/rotation errors. |
| C13-043 | `h t≤n → sq_mx n (mx_of n t)`. | `sq_mx_mx_of`; required before safe nested indexing. |
| C13-044 | On a valid-resolution tree and a coordinate in `sq n`, nested list indexing of `mx_of` equals `get`. | `mx_of_get`. Use proof-domain nested indices or two successful optional lookups. |
| C13-045 | `decomp n mx` first takes/drops `2^n` rows, then maps take/drop `2^n` over each part to obtain four quadrants. | Standard list operations, with one shared row split in the source value expression. No execution-cost identity with a fused splitter is asserted. |
| C13-046 | A square of resolution `n+1` decomposes into four squares of resolution `n`; at resolution zero the shape is exactly `[[x]]` for some `x`. | `decomp_sq_mx`, `sq_mx_0`; these establish recursive domains rather than postulating an arbitrary head. |
| C13-047 | `qt_of 0 [[x]]=L x`; successor `qt_of` decomposes, converts four parts at the smaller resolution, then applies image `Qc`. | `qt_of`; all other zero-resolution list inputs are unspecified. A total Option interface should reject malformed shape, with a checked valid-input bridge. |
| C13-048 | `sq_mx n mx → h(qt_of n mx)≤n`. | `height_qt_of`. |
| C13-049 | `sq_mx n mx → compressed(qt_of n mx)`. | `compressed_qt_of`. |
| C13-050 | Under square shape and bounded coordinates, `get n (qt_of n mx) i j = mx[i][j]`. | `get_qt_of`; retain occurrence/coordinate values, not only a set of pixel values. |
| C13-051 | If `h(Q t0 t1 t2 t3)≤n`, image `Qc` preserves the `get n` observation at every coordinate. | `get_Qc`; the resolution hypothesis is explicit. This is the shared smart-constructor abstraction law used throughout §13.1. |
| C13-052 | Exercise 13.2: define `qt_of_fun : (Nat → Nat → α) → Nat → QTree α` and prove bounded `get n (qt_of_fun f n) i j = f i j`. | Either direct shifted recursive construction or standard `List.ofFn` conversion plus the established shape/index laws. The exercise's stated result is pointwise correctness; also establish its output resolution to make the lookup meaningful. No unjustified constant-time conversion claim. |

## 13.2 Matrix interpretation and algebra: pp. 168–172

The source uses reals, but its displayed algebra does not require their order,
division or completeness. The table names `diag_ma` where the book writes `D`,
and `add`/`mult` where the book uses circled operation symbols. These names are
local to `Quad_Matrix`, not the earlier image operators.

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-053 | Abstract matrix is `Nat → Nat → ℝ`; `sq_ma n a` says entries are zero if either coordinate is at least `2^n`. | Reuse functional/finite `Matrix` with an explicit zero-extension bridge. This predicate is not a finiteness assertion about the function type. |
| C13-054 | `mk_sq n a` keeps entries inside the bounded square and returns zero outside. | Small restriction/extension adapter; requires only `Zero R` and natural comparisons. |
| C13-055 | `D n x = mk_sq n (fun i j => if i=j then x else 0)`. | Finite `Matrix.diagonal (fun _ => x)` followed by zero extension. The outer square restriction is essential. |
| C13-056 | `Qma n a b c d` chooses its block by `<2^n` comparisons and subtracts `2^n` for high row/column coordinates. | Connect to `Matrix.fromBlocks` and `finSumFinEquiv`. The source definition still accepts arbitrary natural indices and arbitrary block functions; do not add unnecessary `sq_ma` hypotheses to its displayed identities. |
| C13-057 | `ma n (L x)=D n x`; successor node observation uses `Qma` on child observations. | This is distinct from image `get`/`mx_of`: a leaf denotes a scalar diagonal, not a constant image block. Valid resolution remains necessary for arbitrary nonleaf observations. |
| C13-058 | Visual block order is upper-left `t0`, upper-right `t1`, lower-left `t2`, lower-right `t3`. | Confirmed p. 169 diagram; retain row/column indexing. A direct image-to-matrix semantic identification would misinterpret a leaf at resolutions above zero. |
| C13-059 | Matrix addition is pointwise; dimension-`n` multiplication is `Σ k<2^n, a i k * b k j`. | `Matrix.add_apply`, `mul_apply`, and `Finset.sum_fin_eq_sum_range` after coordinate bridges. |
| C13-060 | `D n x + D n y = D n (x+y)`. | `add_ma_diag_ma`; `Matrix.diagonal_add` gives the finite identity. |
| C13-061 | `D n 0 + a = a` and `a + D n 0 = a`. | `add_ma_diag_ma_0`, `add_ma_diag_ma_02`; no support premise on `a`. |
| C13-062 | Both products of `a` with `D n 0` equal `D n 0`. | `mult_ma_diag_ma_0`, `mult_ma_diag_ma_02`; finite sums of zeros. |
| C13-063 | `D n x *n D n y = D n (x*y)`. | `mult_ma_diag_ma_diag_ma`; retain scalar multiplication order. |
| C13-064 | Matrix `Qc` compresses four leaves exactly when the off-diagonal labels are zero and the two diagonal labels agree; mixed-child inputs remain a `Q`. | `Quad_Matrix.Qc`, requiring an executable scalar equality capability when claimed executable. It is not image `Qc`. |
| C13-065 | Matrix compression: leaves are compressed; four-leaf nodes are compressed iff the diagonal-collapse condition fails; remaining nodes are compressed iff every child is. | `Quad_Matrix.compressed`; priority of the all-leaf case is material. |
| C13-066 | Matrix addition on two `Q`s adds corresponding children; two leaves add scalars; mixed leaf/node cases add the scalar diagonal only to child positions 0 and 3, retaining positions 1 and 2. | All four clauses of `Quad_Matrix.add`; an image-style leaf broadcast is wrong. |
| C13-067 | Matrix multiplication on two `Q`s uses the standard eight recursive products and four additions, assembled in block order `(s0*t0+s1*t2, s0*t1+s1*t3, s2*t0+s3*t2, s2*t1+s3*t3)`. | `Quad_Matrix.mult` first clause, matching `fromBlocks_multiply`; no Strassen algorithm is specified. |
| C13-068 | Mixed multiplication recursively multiplies all four child blocks with the leaf on the same side; two leaves multiply their scalars. | Remaining three `mult` clauses. Keep left/right order even when generalizing beyond commutative scalars. |
| C13-069 | Mixed cases follow by expanding `L x` as diagonal children `(L x,L 0,L 0,L x)` and eliminating zero terms. | Explicit semantic expansion law, not structural equality of constructors. |
| C13-070 | If both input heights are at most `n`, `ma n (add s t) = ma n s + ma n t`. | `ma_add`; actual operation plus abstraction square. |
| C13-071 | Under the same height premises, `ma n (mult s t) = ma n s *n ma n t`. | `ma_mult`. A standard matrix multiplication theorem alone does not prove the recursive tree implementation. |
| C13-072 | Addition and multiplication each preserve matrix compression on compressed inputs. | `compressed_add`, `compressed_mult`; two separate operation theorems. |
| C13-073 | `ma (n+1) (Qc t0 t1 t2 t3) = ma (n+1) (Q t0 t1 t2 t3)`. | `ma_Suc_Qc`; source statement has no child-height premise, unlike image `get_Qc`. With a valid-domain Lean observation, expose the corresponding domain theorem and explain the restriction. |
| C13-074 | Pointwise addition commutes with forming four blocks. | `add_ma_Qma`; direct reuse of `Matrix.fromBlocks_add` after the full source-coordinate bridge. |
| C13-075 | Adding `D(n+1)x` to four blocks adds `D n x` only to the two diagonal blocks. | `add_ma_diag_ma_Qma`; the symmetric identity `add_ma_Qma_diag_ma` is source support for the other mixed branch. |
| C13-076 | `compressed(Qc t0 t1 t2 t3)` is equivalent to compression of all four inputs. | `compressed_Qc`; source matrix statement is an equivalence. |
| C13-077 | Multiplication of two block matrices expands into the four block formulas in C13-067. | `mult_ma_Qma_Qma`; partition/reindex the finite inner sum. No input-support premise appears in this identity. |
| C13-078 | `D(n+1)x = Qma n (D n x) (D n 0) (D n 0) (D n x)`. | `diag_ma_Suc`; this justifies mixed multiplication, including zero outside the square. |
| C13-079 | Matrix smart construction cannot increase height beyond ordinary `Q`. | `height_Qc_Q`. |
| C13-080 | Both matrix operations have height at most the maximum input height. | `height_add`, `height_mult`; needed for the recursive observation domains. |

## 13.3 Binary region trees in k dimensions: pp. 172–175

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C13-081 | `Box α`/`Split left right` carrier; a round of `k` binary dimension splits refines a `k`-cube by one resolution level, and early homogeneous leaves may represent rectangular boxes. | Exact `Bracketing.Tree` carrier. This is a region partition, not the point-search k-d tree cited in the chapter notes. |
| C13-082 | Height is zero at a box and `max` of child heights plus one at a split; valid resolution for `k` coordinates is `h t≤k*n`. | Reuse shared binary height after its exact equation bridge. The height factor is `k`, not `2^k`. |
| C13-083 | Path `subtree t []=t`; any path in a box returns that box; a nonempty path at a split chooses right for true and left for false. | `subtree`, `subtree_Box`; primitive path traversal is new on the existing carrier. |
| C13-084 | The displayed geometry/prose orders subtrees by increasing coordinates, first left/right then below/above in 2D. | Conflicts with C13-089's tested `<` bit convention; retain the correction/bridge obligation below rather than silently assert both interpretations. |
| C13-085 | Binary compression means both children compressed and not two equally labelled boxes; `SplitC` collapses two equal boxes and otherwise returns `Split`. | `compressed`, `SplitC`; keep semantic predicate and executable equality test separate. |
| C13-086 | Compressed inputs yield compressed `SplitC`. | `compressedI`. |
| C13-087 | If the address length is at least one, `subtree(SplitC l r) bs = subtree(Split l r) bs`. | `subtree_SplitC`; the nonempty-address condition cannot be dropped. At `[]`, collapsing equal boxes changes the tree itself. |
| C13-088 | `cube k n` consists of natural lists of length `k` whose entries are all `<2^n`. | Source defines it using `nlists`. Use length plus element bounds, or a checked vector/`Fin k → Fin(2^n)` bridge. For `k=0`, the domain contains exactly `[]`. |
| C13-089 | A box lookup returns its label; successor lookup builds a Boolean address with `i<2^n`, descends by `subtree`, reduces all coordinates modulo `2^n`, and recurses at `n`. | `KD_Region_Tree.get`, `get_Suc`. Zero-resolution split has no source equation. The lower-half comparison is true, hence follows the right subtree under C13-083. |
| C13-090 | Resolution decreases after one `k`-bit descent: `h(subtree t bs)≤h t−length bs`, hence from `h t≤k*(n+1)` and `length bs=k`, get height at most `k*n`. | `height_subtree`, `height_subtree2`; source support for valid recursive domains. Retain saturated subtraction and the zero-dimension boundary. |
| C13-091 | Zero-resolution `put` replaces a box. Successor `put` modifies the subtree at the same `<`-address, passing residual-coordinate recursive `put` as callback. | `put`; uses the same reflected convention as lookup, so its update theorem remains internally consistent. |
| C13-092 | `modify f [] t=f t`; at a split follow the chosen branch and use `SplitC`; at a box recursively modify a copied box along the remaining address, then join it with the unchanged box on the other side. | All three `modify` clauses. The box case shares its recursive result via `let`; do not evaluate it twice. |
| C13-093 | If `h t≤k*n` and both coordinate lists lie in `cube k n`, then lookup after `put ps a n` gives `a` exactly at `ps` and otherwise the original lookup. | `get_put`; equal dimension and coordinate bounds are supplied by the two cube memberships. |
| C13-094 | `h t≤n*length ps → h(put ps a n t)≤n*length ps`. | `height_put`; no coordinate entry bounds. |
| C13-095 | The same height domain and input compression imply compression of `put`. | `compressed_put`, with source `k=length ps` parameter bridge. |
| C13-096 | If `f` preserves the bound `nk` for every input within it and `h t≤length bs+nk`, then `h(modify f bs t)≤length bs+nk`. | `height_modify`; preserve the universal premise about `f`, not merely its behavior on one selected tree. |
| C13-097 | For equal-length paths `bs'` and `bs`, `subtree(modify f bs t) bs'` equals `f(subtree t bs)` when the paths agree, otherwise `subtree t bs'`. | `subtree_modify`; equal length is essential, including the empty-path base. |
| C13-098 | Compressed `t` and compressed `f(subtree t bs)` imply compressed `modify f bs t`. | `compressed_modify`; weaker than demanding global compression preservation by `f`. |
| C13-099 | Every subtree selected from a compressed tree is compressed. | `compressed_subtree`; address can continue beyond a box. |
| C13-100 | Boolean union: true box absorbs, false box yields the other tree, and two splits recursively union matching sides and use `SplitC`. | `union`, plus its second-box equation `union_Box2`. |
| C13-101 | `max(h s,h t)≤length ps*n` implies lookup of binary union is disjunction of input lookups. | `get_union`; no coordinate range premise is needed. |
| C13-102 | `subtree(union s t) bs = union(subtree s bs)(subtree t bs)`. | `subtree_union`, including `bs=[]`. |
| C13-103 | Binary union has height at most the maximum input height and preserves compression. | `height_union`, `compressed_union`; retain both separate structural observations. |
| C13-104 | Boolean binary trees also represent bounded point sets, and their union agrees with set union. | `points_get`, `points_union`, `points_subset` give the support bridge. Source `mv` assigns zero shift to true, consistent with its reflected address semantics but not with the increasing-coordinate picture. |

## Concrete source discrepancy and boundaries

**Direction conflict, pp. 172–174.** Both the rendered PDF and the pinned
`KD_Region_Tree.thy` contain true-to-right traversal and lower-half-is-true
addresses. Independently evaluating these equations at valid inputs gives

```text
get 1 (Split (Box 0) (Box 1)) [0] = 1
get 1 (Split (Box 0) (Box 1)) [1] = 0.
```

The image explanation says increasing coordinates select the left/below
subtree first. The direct two-level binary encoding of
`Q (L 0) (L 1) (L 2) (L 3)` similarly returns `3,2,1,0` at
`(0,0),(0,1),(1,0),(1,1)`, while ordinary quadtree lookup returns `0,1,2,3`.
These were independently evaluated by a small Python calculation of the
displayed branch equations; they are counterexample targets, not Lean proofs.

The formal get/put and union theorems remain consistent because both sides use
the same reflected interpretation. A faithful reconstruction must explicitly
choose either the printed/source equations with a reflection bridge to the
geometric convention, or a corrected direction convention with proved
correspondence. Changing `<` to its opposite without recording this is not
literal source correspondence. This note makes no implementation choice.

**Partiality and algebraic claims.** Image lookup at a too-small resolution,
list-to-tree conversion of malformed input, matrix observation of a too-tall
tree, and binary lookup with an insufficient resolution are separate domain
failures. Do not conflate them with out-of-bounds coordinate handling, which
the raw lookup clauses do define once the tree/resolution pair is valid.
Likewise, `mx_of` of an image leaf and `ma` of a matrix leaf differ already at
resolution 1 and a nonzero off-diagonal pixel. A checked client should show
this distinction.

The chapter does **not** define time functions or prove a numeric/asymptotic
bound for these operations. Its statements about compression and possible
parallel execution are qualitative motivation. Do not present a traversal
count, big-integer exponent/modulo cost, allocation bound or parallel speedup
as a sourced theorem. The use of standard list or matrix equations establishes
values, not the runtime of the recursive quadtree algorithms.

## Implementation placement and useful connected clients

Keep the new four-child carrier, image observation, compression and pixel/
subimage operations in a domain unit such as `Applications/RegionTrees`.
Reuse `Bracketing.Tree` for the binary region representation; share its height
observation in the narrowest existing tree unit if warranted. The matrix
interpretation belongs with `Applications/Linear`, importing the carrier and
the standard matrix backend. Preserve the two compression policies as distinct
operations. No new general representation or law-transport framework is needed:
existing `Squares.Rep`, `Squares.Square`, products and composition already
provide the integration boundary.

Useful checked clients are the displayed 2×2 indexing example, a nonzero
leaf's differing image/diagonal observations, a pixel update that collapses
four equal quadrants, the cross-quadrant 4×4 extraction, ragged/empty list
matrix rejection, a rational block multiplication including mixed leaf/node
cases, and the explicit one-dimensional direction counterexample/bridge.
Also include `n=0` and `k=0`; these are supported boundaries, not reasons to
add positivity or inhabitance assumptions to every operation.
