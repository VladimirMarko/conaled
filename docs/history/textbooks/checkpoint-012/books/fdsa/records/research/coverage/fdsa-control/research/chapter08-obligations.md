# Chapter 8 source obligations: Red-Black Trees

Status: **queued; source preparation only**. No Lean implementation, accepted
chapter, or checked coverage witness is asserted. This inventory retains both
deletion algorithms, all four figures, Lemmas 8.1–8.6 (including Corollary 8.3),
the three exercises, the separated invariant statements in the companion,
and the mathematical content of the introductory encoding discussion. Read
with `../DECISIONS.md` and Chapters 4–7 inventories.

## Pins and source scope

- Book: July 27, 2026 version, Chapter 8 by Tobias Nipkow, printed pp.95–104
  (PDF pp.101–110).
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  PDF SHA-256
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  Printed pp.95 and 97 were rendered and visually inspected for the two
  source errors recorded below.
- Isabelle mirror:
  <https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21>.
  BSD-3-Clause; `COPYRIGHT` SHA-256
  `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  This is the inspected companion revision, not a claim that it generated
  the pinned manuscript.
- Raw source prefix:
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.
- Shared companion support: `Tree2`, `Tree`, `Tree_Real`, `Isin2`, `Cmp`,
  `Sorted_Less`, `List_Ins_Del`, `Set_Specs`, `AList_Upd_Del`, and `Map_Specs`;
  their inspected revisions/hashes are recorded in Chapters 4–6 inventories.
- Reuse inspection: conaled baseline
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries
  `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean v4.35.0 commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
  The Batteries pin was checked against the project's manifest and local
  dependency checkout. Lean/Batteries files inspected below carry Apache-2.0
  headers. These references are available proof infrastructure, not evidence
  of already integrated chapter coverage.

| Source path | SHA-256 | Inspected content |
|---|---|---|
| `src/HOL/Data_Structures/RBT.thy` | `57240519952cef1a82619d1d1e9721fa31f4ad9e3e7883020f0d68f3ad755ad3` | Colors, root painting, four balancers, joining |
| `src/HOL/Data_Structures/RBT_Set.thy` | `542519dc50a4ca03735f68f36bf6bf666f941a33502b028cf2f939b3119d80c8` | Insertion, joining deletion, all shared invariants, list laws, height bounds, Set interpretation |
| `src/HOL/Data_Structures/RBT_Set2.thy` | `512db7d1698b5c9ce3447ea30a7b493f957655cafeb2e9d5c6437b9f59e14560` | Right-minimum replacement deletion, its helper and invariant proofs |
| `src/HOL/Data_Structures/RBT_Map.thy` | `18aad043c03697c6bd0fb3ad18387dd9030727dceaceee26abb7d5a108ca43ba` | Map update and joining deletion, list/refinement/invariant laws |
| `src/HOL/Data_Structures/Lookup2.thy` | `3969a579629d0b60c01cc44da16866e09653d46f46f2a2d2f115905e06739023` | Lookup in a tree carrying key/value labels plus an irrelevant annotation |
| `src/HOL/Data_Structures/Tree234.thy` | `9720adb1d459f884be3e88217b10af41eae3fe8e96e4eebc8dd624fe15a75d56` | 2-3-4 carrier, inorder, height, equal-height-child invariant `bal` |

The companion filenames reverse the printed presentation order:
**§8.2.2/Figure 8.2 is `RBT_Set2`**, and **§8.2.3/Figure 8.3 is
`RBT_Set`**. The map source chooses joining. Do not let that naming distinction
cause replacement deletion to disappear from the coverage map.

## Observations and exact invariant boundaries

Write `E` for the empty tree, `R(l,a,r)` and `B(l,a,r)` for red and black
internal nodes, `I` for inorder with only the color annotation erased, `h`
for ordinary height, `mh` for minimum height, and `bh` for the left-spine
black-height function. Internal node count is `nodes`; binary external-leaf
count is `leaves=nodes+1=length(I t)+1`. Empty trees have height and black
height zero. A leaf is considered black for `color`, but contributes **zero**
to `bh`.

Let C mean `invc`, H mean `invh`, and C2 mean `invc2=invc ∘ paint Black`.
The book's `rbt` is `C ∧ H ∧ black root`. It does **not** contain key
ordering. Set states additionally require S, strict sortedness of inorder.
Map states require S1, strict sortedness of the first projections of inorder
key/value pairs. An arbitrary list, including duplicates, can be converted
to a structurally valid red-black tree in Exercise 8.3 without being a valid
search tree.

Pure structural functions and their color/height laws need no order on
payloads. Search/update/delete need a lawful key comparator; set equality
branches use actual key equality, while map comparisons examine only the key.
Do not impose an order, equality decision, or default element on map values.
`split_min E` is unspecified in HOL: use an explicit nonempty domain or an
`Option` realization, and prove the correspondence on valid calls. All four
balancers and `join` have total default cases; those defaults must remain
present in their raw recurrences.

Reuse labels: **R** existing proved infrastructure, **P** checked adapter or
transport required, **G** remaining proof/implementation gap, **X**
cross-chapter dependency. A label is not an acceptance certificate.

## Carrier, encoding, invariants, and height: pp.95–97

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-001 | Color has Red and Black; the source carrier is the shared binary tree labelled by `(payload,Color)` (pp.95–96; `RBT`). | R/P Chapters 4–5; Batteries has an equivalent raw carrier with a separate color field. |
| C08-002 | Define R/B notation and `color E=Black`, `color(node _ (_,c) _)=c` (p.96). | P. Distinguish Batteries `isRed`, which uses this leaf convention, from its specially defined `isBlack`. |
| C08-003 | `paint c E=E`; on a node paint replaces only the root color; prove composition `paint c₂ (paint c₁ t)=paint c₂ t` and `color(paint Black t)=Black` (p.96; `paint2`, `color_paint_Black`). | R/P `setBlack`, `setRed`. A universal `color(paint c t)=c` is false for c=Red and t=E. |
| C08-004 | Painting preserves inorder, node count, ordinary height, and minimum height; erasing color retains every payload in the same shape/order (`inorder_paint` and structural support). | R/P. These value observations do not prove any cost equality between representations. |
| C08-005 | Preserve all four p.95 2-3-4 encoding cases and the two permitted orientations of an N3 node, as in the encoding table below; prove inorder preservation. | G/P `Tree234` and Chapter 7. A canonical encoder may choose one N3 orientation, but the other pictured encoding remains a checked local equation. |
| C08-006 | Relate complete 2-3-4 trees to black-root red-black trees: a black root plus its red children forms one multiway node; equal black heights correspond to equal multiway heights. Establish the encoding/grouping invariant correspondence and black-height/height relation. | G. N3 has two orientations, so a fixed canonical encoder and decoder are not mutually inverse on all raw red-black trees without an orientation equivalence or extra data. |
| C08-007 | Correct the p.95 prose count: a 2-, 3-, or 4-child multiway node is encoded using **1, 2, or 3 internal binary nodes**, respectively. Preserve a small checked witness against the printed 2/3/4 count. | G, source correction. An N2 of empty children has one label and encodes to one black internal node. |
| C08-008 | C E holds; C of a node requires C of both children and, when the root is red, both child root colors black (p.96). | R/P `Balanced`; color-only statements remain separate from equal-black-height assumptions. |
| C08-009 | `bh E=0`; a black node has `bh left+1`; a red node has `bh left` (p.97; companion name `bheight`). | P. This function is defined on invalid trees too, and deliberately follows only the left child. |
| C08-010 | H E holds; H of a node requires H of both children and equal child black heights (p.97). | R/P. Exercise 8.2 supplies the missing path-set characterization. |
| C08-011 | `rbt t ↔ C t ∧ H t ∧ color t=Black`, including the valid empty tree (p.96). | P. This is structural validity only; strict search ordering is a separate invariant. |
| C08-012 | Define C2 by blackening the root, prove C implies C2, and characterize the permitted red-red violation as confined to links from the root (p.99; `invc2I`). | R/P `RedRed True` after the H/index bridge. C2 alone does not imply H. |
| C08-013 | Root painting preserves H; blackening restores C from C2; prove the exact black-height effect needed by public wrappers (`invh_paint`, paint definitions). | P. Painting an arbitrary valid node red need not preserve C. |
| C08-014 | `C t ∧ H t -> h t <= 2*bh t + (if color t=Black then 0 else 1)` (p.97; `rbt_height_bheight_if`). | R/P `Balanced.depth_le`, with a separate invariant/carrier bridge. |
| C08-015 | `H t -> bh t<=mh t` (p.97; `bheight_le_min_height`). | P/G. No C or black-root premise is allowed to be added silently. |
| C08-016 | Retain the source's exponential route: `C t ∧ H t -> 2^(bh t)<=leaves t` (`bheight_size_bound`); Chapter 4 also gives `2^(mh t)<=leaves t`. | R/P. The latter and C08-015 can prove a stronger H-only black-height size bound. |
| C08-017 | For rbt t, prove the full real inequality chain `h t<=2*bh t<=2*mh t<=2*log₂(leaves t)` and hence the logarithmic height theorem (p.97; `rbt_height_le`, `rbt_height_le2`). | R/P Chapter 4 and Batteries depth mathematics. Keep the positive log argument and natural/real conversions explicit. Both source proof routes are available; their duplicate final theorem does not require duplicate Lean proofs. |
| C08-018 | Retain a checked counterexample to the p.97 explanatory **equality** with `2*log₂(leaves)`: `B(R(E,0,E),1,E)` has C, H, black root, h=2, bh=mh=1, leaves=3, and `2<2*log₂ 3`. | G, source correction. The displayed formal inequality chain is correct. |
| C08-019 | Exercise 8.1: `C t ∧ H t -> h t<=2*log₂(leaves t)+2` (p.103), without a black-root assumption. | P/G. C08-014–016 yield the stronger +1 bound, which may be proved and then used to derive the printed +2 bound. |

### The p.95 encoding, written without color-dependent typography

Every capital subtree argument below means its recursively encoded, black-root
red-black tree.

| Multiway node | Binary encoding |
|---|---|
| E | E |
| N2(A,a,B) | B(A,a,B) |
| N3(A,a,B,b,C) | B(R(A,a,B),b,C), or B(A,a,R(B,b,C)) |
| N4(A,a,B,b,C,c,D) | B(R(A,a,B),b,R(C,c,D)) |

The 1/2/3 internal-node counts, preserved label counts, and equality of
black heights make the intended statement recoverable despite the prose typo.

## Set search and insertion: pp.97–99, Figure 8.1

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-020 | Empty is E; search is the shared augmented-BST search, ignoring the color and taking exactly one child selected by the comparator (p.97; `Isin2`). | R/P Chapters 5–6. |
| C08-021 | `S(I t) -> isin t x ↔ x∈set(I t)`; establish empty's value and structural laws. | R/P. Membership semantics do not need C, H, or a black root. |
| C08-022 | Implement both insertion balancers with all three ordered branches each, exactly as in the table below (Figure 8.1, p.98; `baliL`, `baliR`). | R/P Batteries `balance1`, `balance2`. The overlapping-case priority is part of the executable definition. |
| C08-023 | Unconditionally, `I(baliL l a r)=I l ++ [a] ++ I r`, and likewise for baliR (`inorder_baliL`, `inorder_baliR`). | R/P Batteries per-balancer `toList` laws. No ordering or structural premise. |
| C08-024 | C2 l and C r imply C of baliL; C l and C2 r imply C of baliR (`invc_baliL`, `invc_baliR`). | P/G. These color-only lemmas are weaker-premise statements than Batteries' combined structural theorems. |
| C08-025 | If `bh l=bh r`, then either insertion balancer has black height `bh l+1` (`bheight_baliL`, `bheight_baliR`). | P/G. C and H are not premises. |
| C08-026 | H l, H r, and equal black heights imply H of either insertion balancer (`invh_baliL`, `invh_baliR`). | P/G. No color premise. |
| C08-027 | Combine C08-024–026 into both displayed p.99 balancer laws: C and H of the result and black height `bh l+1`, with C2 only on the side being repaired (`inv_baliL`, `inv_baliR`). | R/P Batteries `RedRed.balance1/2`; preserve the exact asymmetric hypotheses. |
| C08-028 | Raw `ins x E=R(E,x,E)`; at B compare x with a and use baliL/raw-ins on LT, unchanged B on EQ, baliR/raw-ins on GT; at R use direct R rebuilding on LT/GT and unchanged R on EQ (p.98). | R/P Batteries raw `ins`, after comparator/representative equality and carrier bridges. |
| C08-029 | Under S, `I(ins x t)=ins_list x (I t)` (`inorder_ins`). | R/P existing insertion semantic laws, or source induction. Set duplicates are suppressed; no C/H hypothesis. |
| C08-030 | C t implies C2(ins x t), and old root Black additionally implies C(ins x t) (`invc_ins`). | P/G for the separated color-only theorem. |
| C08-031 | H t implies H(ins x t) and `bh(ins x t)=bh t` (`invh_ins`). | P/G for the separated height-only theorem. |
| C08-032 | Prove the displayed combined raw insertion law of p.99 from C and H, preserving both conclusions and the black-old-root conditional (`inv_ins`). | R/P `Balanced.ins` and the C/C2/H/index bridge. |
| C08-033 | Check the p.98 worked insertion: raw ins 1 into `B(R(E,0,E),2,R(E,3,E))` produces `R(B(E,0,E),1,B(E,2,R(E,3,E)))`, with the displayed intermediate recursive/balancing steps. | G/evaluation witness. Final list equality alone does not establish this trace. |
| C08-034 | Check the p.99 boundary example: `ins 1 (R(E,0,E))=R(E,0,R(E,1,E))` violates C but satisfies C2. | G/evaluation and predicate witnesses. It explains why C2 is necessary. |
| C08-035 | Public `insert x t=paint Black(ins x t)` (p.98). | P. Batteries public insert conditionally blackens using the old root; the source always blackens. |
| C08-036 | Under S, public insert has the ordered-list insertion observation, preserves S, and implements abstract set insertion (`inorder_insert`, shared refinement). | R/P/X Chapters 5–6. |
| C08-037 | `rbt t -> rbt(insert x t)` (p.99; `rbt_insert`, `rbt_insert2`). | R/P. These are two proofs of one property, not two different algorithms. |
| C08-038 | If Batteries is the executable carrier, prove the book-facing public wrapper through existing `RBTree.RBNode.insert_setBlack`: `(t.insert cmp v).setBlack=(t.ins cmp v).setBlack`. | R/P. Inserting into E in the library may yield a red root before this extra blackening; do not claim the unadapted public API has book rbt. |

### Ordered insertion-balancer cases

Rows are tried top to bottom within each function. Variables are payloads or
trees, and the parenthesized triples denote constructor arguments.

| Function and inputs | Result |
|---|---|
| baliL (R(R(t1,a,t2),b,t3)) c t4 | R(B(t1,a,t2),b,B(t3,c,t4)) |
| baliL (R(t1,a,R(t2,b,t3))) c t4 | R(B(t1,a,t2),b,B(t3,c,t4)) |
| baliL t1 a t2 | B(t1,a,t2) |
| baliR t1 a (R(t2,b,R(t3,c,t4))) | R(B(t1,a,t2),b,B(t3,c,t4)) |
| baliR t1 a (R(R(t2,b,t3),c,t4)) | R(B(t1,a,t2),b,B(t3,c,t4)) |
| baliR t1 a t2 | B(t1,a,t2) |

Lean's legacy `Lean.RBNode.balance2` tries the right-left case before the
right-right case, unlike the book and Batteries. When both relevant
grandchildren are red these raw recurrences can produce different trees.
An unconditional primitive-equivalence theorem must use the matching
implementation or explicitly account for the priority difference.

## Deletion balancers and replacement: pp.99–101, Figure 8.2

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-039 | Implement all four ordered branches of baldL and all four of baldR, including their total default R nodes, as in the table below (p.100; `RBT`). | R/P Batteries `balLeft`, `balRight` match the inspected recurrence. |
| C08-040 | Unconditional inorder equations for both deletion balancers, each `I l ++ [a] ++ I r` (`inorder_baldL`, `inorder_baldR`). | R/P existing Batteries `balLeft_toList`, `balRight_toList`. |
| C08-041 | If `color t=Black`, then `bh(paint Red t)=bh t-1` (`bheight_paint_Red`). | P. Natural subtraction is truncated; the E case is valid with 0-1=0. |
| C08-042 | Preserve the separated left height law: H l, H r, `bh l+1=bh r`, and C r imply H(baldL) and black height bh r; the source also proves the variant replacing C r with `color r=Black` (`invh_baldL_invc`, `invh_baldL_Black`). | P/G. The second variant does not assume C of the sibling; it supports joining. |
| C08-043 | Preserve the right height law: H l, H r, `bh l=bh r+1`, and C l imply H(baldR) and black height bh l (`invh_baldR_invc`). | P/G. Keep the one-unit deficit on the correct side. |
| C08-044 | C2 l and C r imply C2(baldL); if the old sibling root r is Black, also C(baldL). Mirror with C l/C2 r and old left root Black for baldR (`invc2_baldL/R`, `invc_baldL/R`). | P/G. No H or black-height equality is assumed in these color-only laws. |
| C08-045 | Lemma 8.4: H l, H r, `bh l+1=bh r`, C2 l, C r imply, for t'=baldL l a r, H t', `bh t'=bh r`, C2 t', and `color r=Black -> C t'` (p.101; `inv_baldL`). | R/P `Balanced.balLeft`, after exact invariant/index translation. |
| C08-046 | Lemma 8.5: H l, H r, `bh l=bh r+1`, C l, C2 r imply, for t'=baldR l a r, H t', `bh t'=bh l`, C2 t', and `color l=Black -> C t'` (p.101; `inv_baldR`). | R/P `Balanced.balRight`. |
| C08-047 | `split_min` of a nonempty node returns (a,r) when l=E; otherwise recursively extracts (x,l') from l and returns x with baldL l' a r if the **old** l is Black, otherwise R(l',a,r) (p.100; `RBT_Set2.split_min`). | G. This right-minimum replacement helper is not the library's joining algorithm. |
| C08-048 | Make `split_min`'s nonempty domain explicit and prove every recursive/public call is in it; retain a theorem relating the Lean realization to the displayed nonempty equations. | P/G. Do not add a globally inhabited payload to totalize E. |
| C08-049 | If split_min t=(x,t') and t≠E, then `x :: I t'=I t` (`RBT_Set2.split_minD`). | G. No S/C/H hypothesis; minimality under S is a consequence. |
| C08-050 | Lemma 8.1: nonempty t, C t, H t, and split_min t=(x,t') imply H t'; if old root Red then `bh t'=bh t` and C t'; if old root Black then `bh t'=bh t-1` and C2 t' (p.99; `inv_split_min`). | G/P shared balancers. All three output clauses and both old-root cases are obligations. |
| C08-051 | Raw replacement del: E→E; LT/GT recursively delete the selected child and use baldL/R exactly when that **old** child is nonempty and Black, otherwise rebuild R; EQ returns l when r=E, otherwise extracts right minimum and chooses baldR or R according to **old** color r (p.100). | G. Neither the parent color nor the returned child color substitutes for the printed tests. |
| C08-052 | Under S, raw replacement del has `I(del x t)=del_list x (I t)` (`RBT_Set2.inorder_del`). | G/P ordered-list laws. The semantic theorem does not require rbt; nonempty helper calls follow the branch tests. |
| C08-053 | Lemma 8.2: C t and H t imply H of raw replacement del and the same old-root-conditional black-height/C/C2 clauses as C08-050 (p.99; `inv_del`, alternative proof `inv_del2`). | G/P. E is included here; natural predecessor black height is zero in that case. |
| C08-054 | Public replacement delete always paints the raw result Black (p.100; `RBT_Set2.delete`). | G/P. Keep this public function distinct from the joining variant. |
| C08-055 | Under S, public replacement delete has the exact ordered-list deletion observation, preserves S, and implements abstract set difference by the singleton x (`RBT_Set2.inorder_delete`). | G/P/X Chapters 5–6. |
| C08-056 | Corollary 8.3: rbt t implies rbt of public replacement delete (p.99; `RBT_Set2.rbt_delete`). | G/P. Root painting is essential to the stated invariant. |
| C08-057 | Instantiate all seven Set-by-Ordered obligations for the replacement implementation, including both structural-preservation and semantic laws (`RBT_Set2.S`). | X Chapter 6. Same search/insert may be shared; replacement deletion remains an explicit consumer. |
| C08-058 | Preserve the p.99 absent-key explanation as a checked raw boundary example: deleting 0 from `B(E,1,E)` returns `R(E,1,E)` before blackening, with unchanged inorder and black height decreased from 1 to 0. | G. Do not assert raw deletion of an absent key is structurally the identity. |

### Ordered deletion-balancer cases

| Function and inputs | Result |
|---|---|
| baldL (R(t1,a,t2)) b t3 | R(B(t1,a,t2),b,t3) |
| baldL t1 a (B(t2,b,t3)) | baliR t1 a (R(t2,b,t3)) |
| baldL t1 a (R(B(t2,b,t3),c,t4)) | R(B(t1,a,t2),b,baliR t3 c (paint Red t4)) |
| baldL t1 a t2 | R(t1,a,t2) |
| baldR t1 a (R(t2,b,t3)) | R(t1,a,B(t2,b,t3)) |
| baldR (B(t1,a,t2)) b t3 | baliL (R(t1,a,t2)) b t3 |
| baldR (R(t1,a,B(t2,b,t3))) c t4 | R(baliL (paint Red t1) a t2,b,B(t3,c,t4)) |
| baldR t1 a t2 | R(t1,a,t2) |

## Joining deletion and cost consequences: pp.101–102, Figure 8.3

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-059 | Implement join's two empty cases, red/red and black/black recursive-inner-child cases with both returned-root branches, and the two mixed-color cases, in source priority order (p.102; table below). | R/P Batteries `append`. |
| C08-060 | Prove termination for the executable two-tree recurrence, e.g. decreasing sum of node sizes; preserve a recursion principle strong enough for source-style invariant/list/cost proofs. | R/P. Result-extensional concatenation is not a replacement for the specified join algorithm. |
| C08-061 | Unconditionally, `I(join l r)=I l ++ I r` (`inorder_join`). | P/G. Batteries supplies per-balancer list laws but no such append-to-list theorem was found in the inspected RBTree sources. |
| C08-062 | H l, H r, and equal black heights imply H(join l r) and `bh(join l r)=bh l` (`invh_join`). | P/G separated H-only statement; source uses the weaker black-sibling left-balancer law C08-042. |
| C08-063 | C l and C r imply C2(join l r); if both old roots are Black, also C(join l r) (`invc_join`). | P/G separated C-only statement. No equal-height premise. |
| C08-064 | Lemma 8.6 combines C08-062–063 under C/H on both inputs and equal black heights, retaining C2 always and C conditionally when both roots Black (p.101; `inv_join`). | R/P `Balanced.append`, with its permitted-violation proposition discharged in the both-Black case. |
| C08-065 | Raw joining del uses exactly the same LT/GT old-child/nonempty/Black branches as replacement del, but EQ is `join l r` (p.102; `RBT_Set.del`). | R/P Batteries `del (cmp x)` uses the matching descent/join scheme. |
| C08-066 | Under S, raw joining del and its always-blackened public delete both have the ordered-list deletion observation (`RBT_Set.inorder_del`, `inorder_delete`). | P/G. Existing ordering/balance erasure theorems do not alone prove exact contents. |
| C08-067 | Prove the same old-root-conditioned raw deletion invariant as Lemma 8.2 for this second algorithm (`RBT_Set.inv_del`). | R/P `Balanced.del`, including its special leaf treatment through `DelProp`. |
| C08-068 | Public joining delete is `paint Black(del x t)` and preserves rbt (`RBT_Set.rbt_delete`). | R/P Batteries `erase` always blackens, so its wrapper has the source convention. |
| C08-069 | Instantiate all Set-by-Ordered obligations for joining deletion (`RBT_Set.S`). | X Chapter 6. Preserve each implementation as a concrete refinement of the same abstract interface. |
| C08-070 | Relate the two deletion implementations observationally under S: equal resulting inorder and abstract set; both preserve rbt when supplied rbt. | P/G cross-implementation bridge. Concrete tree equality is not asserted or needed. |
| C08-071 | To discharge the chapter's search/update efficiency claim, instrument the actual search, ins, split_min, del, join, paint and balancer recurrences with explicitly named charges, then prove the required C08-072/073 height and logarithmic bounds. | G/X, mandatory resource obligation. Neither this chapter nor these companion theories gives a numerical operation-count recurrence to import unchanged. The chosen local/comparator tariff must be explicit; the absence of a printed time function is not a proof waiver. |
| C08-072 | Prove linear-in-height operation bounds in that model: search and insertion traverse one branch; split_min traverses a left spine; join decreases one or both facing subtree paths and admits a bound in `h l+h r`; deletion adds its selected spine and the applicable helper cost. | G. All pattern tests/recolorings/balancer local rewrites must have bounded declared costs; comparator cost is separate unless expressly unit. |
| C08-073 | Derive logarithmic bounds for valid search trees using C08-017; relate stored node count to abstract set cardinality only under S, and to map domain cardinality only under S1. | P/G. Full-tree carrier conversion per update would add linear work and cannot be omitted from a runtime claim. |

### Joining recurrence

The first applicable row wins. `z` below is the single recursive result, so
its computation is shared rather than repeated in the two branch tests.

| Inputs | Recursive action and output |
|---|---|
| E, t | t |
| t, E | t |
| R(t1,a,t2), R(t3,c,t4) | Let z=join t2 t3. If z=R(u2,b,u3), return R(R(t1,a,u2),b,R(u3,c,t4)); otherwise return R(t1,a,R(z,c,t4)). |
| B(t1,a,t2), B(t3,c,t4) | Let z=join t2 t3. If z=R(u2,b,u3), return R(B(t1,a,u2),b,B(u3,c,t4)); otherwise return baldL t1 a (B(z,c,t4)). |
| t1, R(t2,a,t3) | R(join t1 t2,a,t3) |
| R(t1,a,t2), t3 | R(t1,a,join t2 t3) |

## Map implementation: pp.101–103, Figure 8.4

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-074 | Map carrier is RBT of `(key,value)`, hence source binary labels are `((key,value),Color)`; the abstraction is map_of of inorder and S1 orders only keys. | R/P/X Chapter 6. Color erasure must retain both key and value. |
| C08-075 | Lookup E returns None; at a labelled node compare the query with the stored key, select l/r, and return Some stored value on EQ (p.102; `Lookup2`). | R/P shared augmented-map search. |
| C08-076 | Under S1, lookup equals the abstract finite partial map observation; no structural rbt premise is needed for this equality. | R/P/X Chapter 6. No order or default value on the value type. |
| C08-077 | Raw upd inserts a red `(x,y)` node at E; the B/R LT/GT cases follow raw ins with key comparisons and the same balancers; EQ replaces the complete stored pair with `(x,y)` while retaining the root color (Figure 8.4). | R/P Batteries `ins` on pairs compared by key has the required replacement behavior. |
| C08-078 | Under S1, `I(upd x y t)=upd_list x y (I t)` (`RBT_Map.inorder_upd`). | P/G exact ordered association-list bridge. Equality of key sets alone would miss updated values. |
| C08-079 | C t implies C2(upd x y t), and old root Black implies C of the result (`invc_upd`). | P/G separated color-only theorem, independent of ordering and H. |
| C08-080 | H t implies H(upd x y t) and unchanged black height (`invh_upd`). | P/G separated height-only theorem. |
| C08-081 | Public update always paints Black; prove exact ordered-list update semantics and rbt preservation (`inorder_update`, `rbt_update`). | R/P. Apply the public-insertion root adapter if reusing Batteries. |
| C08-082 | The companion map deletion uses joining: compare x with `fst ab`, otherwise preserve the set algorithm's old-child tests, generic balancers, and join of full payloads (`RBT_Map.del`, `delete`). | R/P. Replacement values and colors must not be confused with ordered keys. |
| C08-083 | Under S1, raw and public map deletion have the key-directed association-list deletion observations (`RBT_Map.inorder_del`, `inorder_delete`). | P/G. Requires strict key uniqueness, not lexicographic sortedness of entire pairs. |
| C08-084 | Prove raw map deletion's H/C/C2/black-height law and public rbt preservation (`del_invc_invh`, `rbt_delete`). | R/P using payload-parametric balancer/join proofs. |
| C08-085 | Instantiate all Map-by-Ordered laws, including empty/lookup/update/delete semantics and invariant preservation (`RBT_Map.M`). | X Chapter 6, plus map cardinality/height bridge when using C08-073. |
| C08-086 | Retain the p.102 claim that replacement deletion also adapts to maps: compare only keys, extract the entire successor pair with the same nonempty split_min, and prove key-directed contents and rbt preservation. | G/P. The supplied map source implements only joining; a generic parameterized proof may discharge this alternative without duplicating structural proofs. |
| C08-087 | Make payload parametricity explicit: paint, all balancers, and join inspect only tree shape/colors, so their inorder and structural results apply to key/value labels without extra value assumptions. | R/P. This is the concrete reuse claim of §8.3, not merely informal similarity. |

## Exercises 8.2–8.3: p.103

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C08-088 | Define the set of path black heights: bhs E={0}; at a node let Hs=bhs l∪bhs r and use successor-image Hs for Black, otherwise Hs (Exercise 8.2). | G. A finite-set implementation is acceptable with a checked bridge to this set observation. |
| C08-089 | Establish support facts needed for the reverse direction: bhs is nonempty, `bh t∈bhs t`, and successor image is injective on sets; characterize singleton union when both sets are nonempty. | R/P finite-set/set algebra plus G tree lemmas. These facts need neither C nor a black root. |
| C08-090 | Exercise 8.2 forward direction: H t implies `bhs t={bh t}`. | G. Preserve the exact singleton equality, not only containment. |
| C08-091 | Exercise 8.2 reverse direction: `bhs t={bh t}` implies H t, completing the stated iff. | G. This includes deriving equal child black heights and each child's invariant from the path-set equation. |
| C08-092 | Exercise 8.3: define an executable `rbt_of_list` with linear time, following Chapter 7's bottom-up construction (p.103). One concrete solution is to encode its complete 2-3 tree using N2→B and N3→B with a red left child, as in the p.95 table. | X Chapter 7/G. Repeated set insertion does not answer the linear-time, exact-list requirement. |
| C08-093 | Prove `I(rbt_of_list xs)=xs` for every list, including empty and repeated values. | G/P Chapter 7 inorder preservation plus a proved encoding bridge. |
| C08-094 | Prove `rbt(rbt_of_list xs)` for every list. For the proposed route, prove complete 2-3 input gives C/H/black-root encoding. | G/P. No sortedness assumption is allowed here. |
| C08-095 | For that route, establish `bh(encode23 t)=h23 t` under completeness and `nodes(encode23 t)=keys23 t` unconditionally; retain the exact recursive encoder and its traversal count. | G/support. An N3 creates two binary internal nodes, so using source 2-3 internal-node count as output size would be wrong. |
| C08-096 | Prove an explicit linear bound in the chosen call model. For the proposed two-stage route, encoder calls equal `nodes23+externalLeaves23=nodes23+keys23+1<=2*keys23+1`; combining Chapter 7's `T23(n)<=3n+3` gives the candidate `T<=5n+4` when composition adds no wrapper charge. | G. This is an unproved candidate bound for later Lean work, not accepted validation. Any different local/constructor charges require their own constants and correspondence. |
| C08-097 | Relate the conversion to search-tree validity: strict sorted input gives S of the output; arbitrary duplicate input still gives structural rbt and exact inorder but may fail strict search ordering. | P/G. The two-element list `[1,1]` is a useful checked boundary witness. |
| C08-098 | Discharge the still-open Chapter 5 balanced interval augmentation using an actual chosen balanced family, if red-black trees are selected: maintain exact attained subtree maximum through every rewrite/recoloring, prove erasure to these algorithms, preserve interval search semantics, and derive its height/cost bounds. | X C05-085/C05-090. This is a cross-chapter integration obligation, not something established by ordinary red-black validity alone. |

Exercise 8.1 is C08-019. Chapter Notes (p.104) give provenance and historical
alternatives; they do not specify an additional algorithm or a new exact
mathematical theorem to substitute for either required deletion variant.

## Detailed library reuse and limits

### Closest source match: Batteries.Recycling.RBTree

At the pinned Batteries revision, inspect `Basic.lean`, `WF.lean`,
`Lemmas.lean`, and `Depth.lean` under `Batteries/Recycling/RBTree/`.
The namespace prefix below is `RBTree.RBNode`. These Apache-2.0 files credit
Leonardo de Moura and Mario Carneiro for the raw implementation and Mario
Carneiro for the proof/depth development. Cite the dependency and retain its
license when adapting code; these notes do not copy its implementation.

`RBTree.RBNode α` has constructors nil and node(color,left,value,right).
Its raw `balance1`, `balance2`, `balLeft`, `balRight`, `append`, and root
painting have the same inspected branches as the corresponding book
functions. Set `ins` replaces the resident representative on comparison
EQ, which equals the old payload when the comparator's EQ means actual
set-key equality. With key/value payloads this replacement is exactly what
map upd requires.

Two predicates need careful translation:

- `Balanced t c n` combines C and H with actual root color c and black
  height n. A red node requires both children Balanced black n; a black
  node accepts either child root color at equal n and has black height n+1.
  Nil is Balanced black 0. It does **not** include ordering.
- `RedRed p t n` is either Balanced, or a red root with independently
  Balanced equal-black-height children, where proposition p authorizes the
  possible red-red root violation. It also does not include ordering.
  Under the index bridge, `RedRed True` corresponds to H together with C2.

The relevant already proved laws are:

| Library declaration | Exact reusable premise/conclusion pattern |
|---|---|
| `RedRed.balance1` | l.RedRed p n and r.Balanced c n imply some result root color balanced at black height n+1. |
| `RedRed.balance2` | l.Balanced c n and r.RedRed p n imply some result root color balanced at black height n+1. |
| `Balanced.balLeft` | l.RedRed True n and r.Balanced cr (n+1) imply result.RedRed (cr=red) (n+1). |
| `Balanced.balRight` | l.Balanced cl (n+1) and r.RedRed True n imply result.RedRed (cl=red) (n+1). |
| `Balanced.append` | l.Balanced c1 n and r.Balanced c2 n imply result.RedRed (c1=black → c2≠black) n. If both roots Black, `RedRed.of_false` yields full balance. |
| `Balanced.ins` | t.Balanced c n implies `(ins cmp v t).RedRed (t.isRed=red) n`. |
| `Balanced.del` | t.Balanced c n implies `(t.del cut).DelProp t.isBlack n`. Genuine black nodes lose one black level into RedRed True; red roots and nil retain a Balanced result at n. |
| `Balanced.erase` | t.Balanced c n implies some n' with `(t.erase cut).Balanced black n'`. |
| `RedRed.setBlack` | t.RedRed p n implies some n' with `(setBlack t).Balanced black n'`. |
| `insert_setBlack` | `(t.insert cmp v).setBlack=(t.ins cmp v).setBlack`, unconditionally. |

Batteries `isRed` treats nil as black, like the source `color`.
Batteries `isBlack` intentionally treats nil as red, so testing it for
black matches the book's **nonempty and black** child test. Erasure uses
the matching always-blackened public wrapper. Public insertion uses
conditional root blackening and needs C08-038.

Ordering has its own predicate `Ordered cmp t`, with recursive strict
left/right conditions. `cmpLT cmp x y` is packaged to assume a lawful
transitive comparator locally; under `Std.TransCmp cmp`, `cmpLT_iff`
exposes `cmp x y=.lt`. Available laws include `Ordered.balance1/2`,
`Ordered.balLeft/Right`, `Ordered.append`, `Ordered.ins`,
`Ordered.insert`, `Ordered.del`, and `Ordered.erase`. The balancer/join
ordering laws use a separating pivot together with ordered inputs. The
book's removed root supplies that pivot in deletion.

`ordered_iff` characterizes Ordered by pairwise strict comparison on
`toList`; `Ordered.toList_sorted` supplies its forward form. The theorem
actually present is **`WF_iff`**:
`t.WF cmp ↔ t.Ordered cmp ∧ ∃ c n, t.Balanced c n`.
The module introduction still mentions the older spelling `WF_def`.

`Lemmas.lean` has unconditional `setBlack_toList`, `setRed_toList`,
`balance1_toList`, `balance2_toList`, `balLeft_toList`, and
`balRight_toList`; `size_eq` relates size to list length. Insertion has
`insert_toList_zoom`, `exists_insert_toList_zoom_nil`,
`exists_insert_toList_zoom_node`, and `mem_insert`.

The inspected Recycling/RBTree modules did **not** supply an
`append_toList`, exact deletion-to-list equation, or erasure membership
law. Ordering/balance preservation and zipper facts such as `zoom_del`
are useful inputs, but are not substitutes for C08-061/C08-066/C08-083.
The split_min/replacement variant also remains a distinct algorithm.
Likewise, combined Balanced laws do not automatically prove source
C-only, H-only, or black-height-only statements with weaker hypotheses.

`Depth.lean` proves:

- `Balanced.depth_le`: depth ≤ depthUB c n, where red gives 2n+1 and
  black gives 2n;
- `Balanced.le_size`: `2^(depthLB c n)<=size+1`, with red n+1 and black n;
- `Balanced.depth_bound`: `depth<=2*(size+1).log2`;
- `WF.depth_bound`: the same bound from WF.

These are substantial verified height results. Book-facing real-log
statements require the existing natural/real logarithm bridge and proof
that carrier translation preserves size and height. They do not establish
an operation-count recurrence. Use the reusable carrier directly or use
the equivalence for proof transport; wrapping every executable operation
with a full-tree conversion incurs work that C08-073 must count.

### Other inspected standard carriers

`Lean/Data/RBMap.lean` and `Lean/Data/RBTree.lean` provide legacy red-black
algorithms. Their `WellFormed` is an operation-reachability predicate and
does not by itself expose the book's C/H characterization. Its `balance2`
priority differs as recorded above. Both modules are deprecated since
2026-06-01, recommending Std TreeMap/TreeSet. Old Batteries Data/RBMap
paths are deprecated forwarding shims; the substantive verified RB
implementation is the Recycling path inspected here.

`Std.TreeMap`/`DTreeMap` use size-balanced trees with cached size,
delta=3 and ratio=2, not red-black colors. Their strong semantic laws
(`mem_insert`, `mem_erase`, `getElem?_insert`, `getElem?_erase`) may support
an abstract-map client but do not verify the book's recurrences.
Std's `minView`, `maxView`, and `glue` provide replacement-like operations;
glue chooses the side using sizes, so this is not `RBT_Set2`'s fixed
right-minimum red-black algorithm.

## Source defects, exclusions, and recovery handoff

1. **Printed p.95 node count:** the diagrams and stored-key counts require
   1/2/3 internal binary nodes for 2/3/4 children. Preserve both the
   corrected count and the one-node counterexample (C08-007).
2. **Printed p.97 equality:** the explanatory equality with
   `2*log₂(leaves)` overstates an upper bound. The immediately displayed
   formal chain is correct, as are both companion height theorems.
   Preserve the two-node strict-inequality witness (C08-018).
3. **Leaf/color conventions:** black external leaves have black height
   zero, and paint Red cannot make E red. Library `isBlack` has a different
   deliberately useful empty convention; translate it instead of renaming
   it to source color without a proof.
4. **Value and invariant hypotheses:** list-preservation laws for the
   balancers/join are unconditional; deletion/insert sorted-list semantics
   require strict ordering; the structural laws require their separately
   stated C/H conditions. Requiring the full valid-set invariant everywhere
   would lose several printed modular claims.
5. **Coverage is still queued:** library results, the proposed linear
   conversion, and suggested cost bounds are a preparation map. Each
   eventual coverage entry needs an exact Lean declaration, correspondence
   for the actual algorithm, matching validation, and both required review
   axes on an immutable candidate. Neither this inventory nor Markdown
   derivations of exercise answers complete a Lean obligation.

All 98 numbered entries are source or explicitly identified integration/
support obligations. The source models and theorem statements may be
recovered from this original inventory and the pinned BSD/Apache sources
without packaging the full book manuscript. The mutable PDF URL plus its
hash remains explicit; no immutable official URL for this exact PDF has
been established.
