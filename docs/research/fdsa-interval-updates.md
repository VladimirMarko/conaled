# Interval-tree updates and their separate correctness conditions

This increment implements **FDSA-5-75 to FDSA-5-78** from the unchanged
[Chapter 5 obligation inventory](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
It supplies literal insertion, paired leftmost extraction, successor deletion,
erasure bridges, strict-list refinements and cache preservation. The definitions
extend the existing [interval foundations](fdsa-interval-foundations.md) on
`BinaryTree (κ × α)`, retaining separate universes for complete keys and endpoints
and an arbitrary interval projection `iv : κ → IntervalKey α`.

## Primary correspondence

The primary exposition is Tobias Nipkow's [Functional Data Structures and
Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
July 27, 2026 version, printed pages 73–74 (PDF pages 79–80). The consulted PDF
has SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion is
[Interval_Tree.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Interval_Tree.thy)
at revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, SHA-256
`0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2`.
The source's insertion/deletion section defines `insert`, `split_min` and
`delete`, and states `inorder_insert`, `split_minD`, `inorder_delete`,
`inv_max_hi_insert`, `inv_max_hi_split_min` and `inv_max_hi_delete`.
The local canonical inventory has SHA-256
`f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad`.
Its `sorted` convention is **strict** complete-key order.

These are local Lean proofs with a checked program correspondence, not an
Isabelle execution claim or an assertion that lost unqualified code was
reconstructed exactly. Lean is pinned to 4.35.0 and Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Canonical row | Local owners and principal declarations | Correspondence |
| --- | --- | --- |
| FDSA-5-75 | [Insert](../../Applications/Search/IntervalTree/Insert.lean): `insert`, `insert_nil`, `insert_node`, raw branch equations and `insert_eq_root` | Literal high in the empty branch; smart reconstruction only on LT/GT; original annotated node in the lawful EQ branch |
| FDSA-5-76 | [Leftmost](../../Applications/Search/IntervalTree/Leftmost.lean): `splitMin`, `splitMinNonempty`, domain/specification laws, `erase_splitMin`, `splitMin_inorder`, `join`; [Delete](../../Applications/Search/IntervalTree/Delete.lean): `delete`, branch equations, `erase_delete` | Single paired extraction with an explicit nonempty source domain; successor deletion smart-rebuilds changed ancestors and the new root |
| FDSA-5-77 | [Refinement](../../Applications/Search/IntervalTree/Refinement.lean): `inorder_insert`, `inorder_delete`, `strict_inorder_insert`, `strict_inorder_delete` | Exact existing ordered-list insertion/deletion under strict erased inorder, with no cache premise |
| FDSA-5-78 | `insert_cacheValid_of_singleton`, `insert_cacheValid`, `splitMin_cacheValid`, `join_cacheValid`, `delete_cacheValid` | Structural preservation of exact recursive cache equations, with no BST premise |

The connected cases live in
[IntervalTreeUpdates](../../Examples/IntervalTreeUpdates.lean), which is imported
by `SquareApplications`. Its imports retain the earlier geometry and foundation
examples without changing their source.

## Literal programs and explicit domains

Insertion into nil stores `(x, (iv x).high)` directly. This is observably
different from smart construction when `Max` is arbitrary data. On a nonempty
node, the first strict comparison recurses left and the second recurses right;
both branches smart-rebuild the ancestor. The fallback returns the complete
original node, including its old cache. The raw interface needs only `LT κ`
and decidable strict comparison. At that generality, two false comparisons
need not mean equality. The named same-key equation uses `LinearOrder κ` to
supply irreflexivity; the raw branch equations expose their exact premises.

`splitMin` returns `none` exactly on nil. A node with empty left child returns
its complete key and unchanged right subtree. Otherwise the program traverses
the left spine, returns the extracted key with the residual, and smart-rebuilds
each changed ancestor. `splitMinNonempty` obtains its pair from this optional
result using a proof that the input is nonempty. No arbitrary default key is
introduced, and neither interface requires key equality or key order.
The historical name `splitMin` describes the ordered use; the raw program
extracts the **leftmost** key, which need not be the least.

`join` is the successor deletion callback. Empty right returns the entire left
subtree unchanged. Nonempty right is extracted once through the proved-domain
wrapper; the new root uses `node iv left successor residual`. Its cache is the
maximum of the successor's high and both subtree readers. In particular, it
is not assigned only the successor's own high. `delete` uses this callback in
its raw fallback, smart-rebuilds LT/GT ancestors, and returns nil on nil.
The existing generic `OrderedTree.deleteWith` can customize its equality
callback but hardcodes plain node reconstruction in the search branches.
It therefore cannot directly execute these annotated updates. A narrow
interval recurrence plus the erasure bridge preserves reuse of its proofs.

## Proof reuse and hypothesis boundaries

`Trees.Cached.erase` forgets annotations while preserving all complete keys,
shape and occurrences. `erase_splitMin` states equality of optional pairs:
the extracted complete key is retained and only the residual tree is erased.
It identifies the program with the existing `Trees.extractLeftmost`.
`splitMin_inorder` then follows directly from the shared raw extraction theorem:

`x :: inorder (erase residual) = inorder (erase input)`.

This identity requires only a successful result, with no cache or ordering
premise. `erase_join` uses the successful pair and `Trees.joinLeftmost_of_extract`;
`inorder_join` reuses the established concatenation theorem. Substantial list
correctness is not re-proved by a second interval-specific induction.

`erase_delete` targets `OrderedTree.deleteBy id` and retains raw `LT` and
`DecidableLT`. The existing `OrderedTree.insert` owner has a `LinearOrder`
interface, so `erase_insert` uses that key typeclass. Neither erasure bridge
assumes the input tree is ordered. This typeclass boundary is distinct from
the strict-inorder premise needed for list correctness.

The two list refinements compose erasure with `OrderedTree.inorder_insert`
and `OrderedTree.inorder_delete`. Their target is the existing
`OrderedList.insert`/`delete`, including deletion's actual scan through unequal
heads and removal of the first equality. Strict output follows from those
same list operations' preservation laws. Invalid annotations do not affect
the result because these proofs have no cache hypothesis.

| Result family | Endpoint structure | Key structure and other premises |
| --- | --- | --- |
| Raw insertion/deletion equations | `LE`, `Max`, `Bot` | `LT`, `DecidableLT`; explicit branch premises |
| Split/domain/join equations and erasure/inorder | `LE`, `Max`, `Bot` | No key structure; successful-result/nonempty premise where needed |
| Delete erasure | `LE`, `Max`, `Bot` | `LT`, `DecidableLT`; no tree invariant |
| Insert erasure | `LE`, `Max`, `Bot` | `LinearOrder`; no tree invariant |
| Insert/delete strict-list refinements | `LE`, `Max`, `Bot` | `LinearOrder` and strict erased inorder; no cache premise |
| Split residual/join/delete cache preservation | `LE`, `Max`, `Bot` | Valid input caches; deletion additionally needs raw decidable comparison |
| Generic insertion cache preservation | `LE`, `Max`, `Bot` | Raw decidable comparison, valid input caches, and the inserted key's singleton equation |
| Canonical insertion cache preservation | `LinearOrder`, `OrderBot` | Raw decidable comparison and valid input caches |

The generic insertion law uses only

`(iv x).high = max (iv x).high (max ⊥ ⊥)`.

The quantifier is fixed at the inserted `x`; unrelated keys need no such law.
`insert_preserves_cacheValid_iff` also proves necessity by considering the
valid empty input. The canonical corollary discharges the law using the
linear-order maximum and bottom equations. The other structural cache proofs
need no algebraic maximum laws: they preserve the local equations supplied
by `CacheValid` through the existing smart-constructor laws.

No theorem here needs injectivity of `iv`, a projected-low compatibility law,
or equality of endpoint and key universes. Greatest-endpoint meaning remains
the separately established canonical maximum theorem. Local validity with
arbitrary `Max` data alone supplies no such semantic guarantee.

## Discriminating connected cases

The calculations below were specified independently before implementation.
Exact shape equations inspect the literal program. Positive validity and
contents results then use the public generic theorems with proved hypotheses.
They do not claim allocation identity, physical sharing, running time or
search correctness.

| Case | Independent expected result | Checked connection and boundary |
| --- | --- | --- |
| O01 | Insert `[2,5]` into nil stores 5; duplicate insertion into a leaf cached 99 leaves 99; deleting absent `[0,0]` repairs that visited leaf to 5; empty extraction is absent | Literal equations, `insert_eq_root`, canonical insertion preservation, nonempty extraction specification; malformed matching leaf remains invalid |
| O02 | Insert `[4,40]` into the seven-node tree along left/right/left, raising caches to 40; deleting it restores the exact original tree | `inorder_insert`, `inorder_delete`, strict-output and cache-preservation laws; complete resulting inorder checked |
| O03 | Duplicate insertion preserves the matching leaf but repairs its ancestor from 100 to 3; another insertion leaves a corrupt left sibling at 99 | Exact shapes, strict-list refinement, explicit validity of the repaired tree and invalidity of the untouched descendant |
| O04 | Extract `[1,40]`; the residual reader falls from 40 to 7 | Successful-pair raw inorder transport and `splitMin_cacheValid` |
| O05 | Malformed unordered input extracts leftmost `[5,5]`, although `[1,1]` is present and smaller; the residual reader 1 misses high 2 | Raw inorder transport still applies; input/order and residual/cache failures are proved |
| O06 | Deleting `[8,9]` chooses successor `[10,10]`, but the new root cache remains 30; empty right returns an invalid left subtree verbatim | Successful extraction, successor-root equation, join/delete cache laws and exact list refinement |
| O07 | Removing highs 30 then 20 gives root readers 20 then 18 | Both exact shapes, contents, strictness and cache-preservation derivations |
| O08 | Equal-low keys with caches 99 still insert/delete to the specified strict key lists, while outputs remain cache-invalid | Both list refinements require only strict complete-key inorder; both output strictness and invalidity are checked |
| O09 | A cache-valid unordered tree stays cache-valid under updates; directed delete can miss a stored key and directed insert can add a duplicate | Generic cache preservation, concrete failures of unconditional list laws, and duplicate-tree failure of unconditional set difference |
| O16 | Two higher-universe indexed keys project to `[2,8]`; inserting both, splitting, and deleting each retains their distinct identities | Public insert/split/delete validity and strict-list laws; deleting one key leaves the interval in the image, unlike deleting that interval from the image |
| O17 | Inserting `[-7,2]` into the negative tree raises its reader to 2; deletion restores the exact tree and reader −1 | Canonical cache preservation and both list refinements over `WithBot Int`; the true empty bottom differs from numeric zero |
| X01 | With raw `Max Nat` constantly 100, literal insertion stores 5 and smart construction stores 100 | Same erasure but different annotations; literal cache invalid, smart cache valid but unattained, and the generic preservation equivalence rejects insertion preservation |

The main seven-node fixture has keys `[1,2]`, `[3,6]`, `[5,20]`, `[8,9]`,
`[10,10]`, `[15,18]`, `[22,30]`, with the fourth as root. Its left subtree
maximum is 20 and right subtree maximum is 30. This makes the deep insertion,
successor replacement and successive maximum decreases distinct obligations.
The negative fixture reuses the existing `WithBot Int` foundation example;
the indexed fixture reuses its `ULift` complete-key carrier and noninjective
projection. The nonlawful maximum instance is local to its example section;
it never supplies a canonical maximum theorem's instance.

## Remaining work and integration boundary

This increment has four canonical rows. **FDSA-5-79 remains open**: it requires
the combined cache/order invariant, empty and equality-membership semantics,
insert/delete set semantics and an actual interval-set contract with overlap
observation. The four displayed update corollaries alone do not establish it.
FDSA-5-80 to FDSA-5-84 cover the overlap and point-search work; FDSA-5-85 to FDSA-5-90 cover balanced
augmentation and sweep-line work; FDSA-5-91 to FDSA-5-94 cover distance algorithms. All
later FDSA chapters/appendices and remaining PFDS work retain their existing
scope. This note establishes neither full Chapter 5 nor all-books completion.

The donor source extends the preserved shared tree, ordered-list and ordered-tree
owners. Their presence, the earlier path-module relocation, the donor executable
configuration and the union of donor/receiving aggregate imports must be retained
in receiving integration. Exact dependency pins or a small textual intersection
do not establish receiving semantic acceptance. Focused candidate checks and the
independent Standards/Spec reviews are recorded with the checkpoint evidence;
the actual receiving union, whole-library build and exhaustive integrated audit
remain separate receiving obligations.
