# Chapter 4 exercise Phase 1 frozen contracts

Status: frozen before source creation; UNCOMPILED. This is source preparation in the existing full-Chapter-4 implementation/review loop. It is not acceptance or a new review loop. Whole-chapter base remains `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`; source parent is `5b17c8e4a962a8e79251eda1b5f94f97a3d4cc34`.

## Source and instruction basis

The full Chapter 4 inventory was read in three bounded portions (receipts 8a7c4d, 893087, 0085d5), SHA-256 `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`. Complete pinned primary Chapter 4 PDF pages 53–64 were read through text page boundaries (receipts e72d28 and b7fcae). Primary PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; extracted text SHA-256 `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The manuscript stays outside deliverables.

REQUEST, AGENTS, implementation, EDD, worked-example, architecture, domain, glossary, review-loop, and ADR 0001/0010 instructions were read. An initial globally truncated instruction read was supplemented by complete bounded recoveries (99eb55 and bc87b8). Both preflight reports and the structural phase-1 contract were read completely (bbc3f6 and a1c83c). No compiler red phase is claimed: the path-presence baseline is the actual interface-absence evidence.

## Levels: C04-023 through C04-026

Carrier: Mathlib `BinaryTree α`, arbitrary `α : Type u` without typeclass assumptions. Names live in `Trees`.

```
def level : BinaryTree α → Nat → List α
-- nil,k = []; node a l r,0 = [a]; node a l r,k+1 = level l k ++ level r k

def mergeLevels : List (List α) → List (List α) → List (List α)
-- [],ys = ys; xs,[] = xs; x::xs,y::ys = (x ++ y)::mergeLevels xs ys

def levels : BinaryTree α → List (List α)
-- nil = []; node a l r = [a] :: mergeLevels (levels l) (levels r)

level_nil (k : Nat) : level (.nil : BinaryTree α) k = []
level_node_zero (a : α) (l r : BinaryTree α) : level (.node a l r) 0 = [a]
level_node_succ (a : α) (l r : BinaryTree α) (k : Nat) :
  level (.node a l r) (k+1) = level l k ++ level r k
levels_nil : levels (.nil : BinaryTree α) = []
levels_node (a : α) (l r : BinaryTree α) :
  levels (.node a l r) = [a] :: mergeLevels (levels l) (levels r)
mergeLevels_length (xs ys : List (List α)) :
  (mergeLevels xs ys).length = max xs.length ys.length
mergeLevels_getD (xs ys : List (List α)) (k : Nat) :
  (mergeLevels xs ys).getD k [] = xs.getD k [] ++ ys.getD k []
levels_length (t : BinaryTree α) : (levels t).length = t.height
levels_getD (t : BinaryTree α) (k : Nat) : (levels t).getD k [] = level t k
levels_getElem? (t : BinaryTree α) (k : Nat) (hk : k < t.height) :
  (levels t)[k]? = some (level t k)
```

`levels` and `mergeLevels` algorithms have no natural-number argument/arithmetic and traverse each input tree structurally once; lists are merged with append, so no linear total-runtime theorem is claimed. Proof indices and length/height arithmetic are observations, not algorithm parameters.

Independent expected fixture, before source: root9; left child3 with left leaf8; right child7 with left child4 whose right leaf is6, and right leaf5. Its ordered levels must be `[[9], [3,7], [8,4,5], [6]]`, height4, third level `[8,4,5]`, and out-of-range level4 empty. A repeated-label two-level tree with label5 at root and both children has `[[5],[5,5]]`. Empty tree over `Empty` has no levels. Examples must use the general length/index/getD laws as well as exact evaluations, including the repeated and empty cases. The asymmetric fixture detects reversed order, missing descendant levels, and dropped unmatched suffixes.

## Rose: C04-029 through C04-030

New matching carrier, in namespace `Trees`:

```
inductive Rose (α : Type u) where
| node (label : α) (children : List (Rose α))
```

Public operations and laws, in namespace `Trees.Rose`, with no equality, ordering, or inhabitance assumptions:

```
def mirror : Rose α → Rose α
mirror_node (a : α) (children : List (Rose α)) :
  mirror (.node a children) = .node a ((children.map mirror).reverse)
mirror_mirror (t : Rose α) : mirror (mirror t) = t
```

Mirroring keeps each label, mirrors every descendant and reverses the finite child list at every node. Implementation may use proof-bearing child membership solely to discharge structural termination; the public node equation is the ordinary ordered-list equation. The involution proof must quantify over every finite rose tree and justify the nested recursive calls.

Independent expected fixture, before source: root9 with children `[node3 [node1 [], node2 []], node7 [node6 [node5 []]], node8 []]`. Mirror has children `[node8 [], node7 [node6 [node5 []]], node3 [node2 [], node1 []]]`. This detects both top-level reversal and descendant reversal. A root with two identically labelled leaf children preserves both occurrences. The nontrivial fixture must consume the public involution theorem rather than proving only a closed evaluation.

## Handoff gates and honest limitations

Allowed edits are the four module/example pairs assigned to this author. Coordinator owns entrypoint/maps/correspondence and all compilation. Each pair will receive source/public-statement identities, a local Conventional Commit (#174), and an explicit UNCOMPILED handoff. All 76 Chapter 4 obligations, executable enumeration with duplicate-free output for repeated labels, reconstruction with exact distinctness condition, full validation/audit, two independent reviews, and immediate candidate verification remain mandatory. No source-only result is accepted.
