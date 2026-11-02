# FDSA shared ordered-tree observations

This note records the shared structural ordering interface used by the book's
binary search trees, keyed maps and later balanced representations. It uses
the existing Mathlib `BinaryTree` carrier and `Trees.inorder`. The predicate,
its observation laws, and the ordinary/cached rotation adapters are separate
from search algorithms, balancing, cached-summary validity and execution cost.

This is an uncompiled source draft. Its inherited tree modules and its new
proofs still require the applicable integrated build, exhaustive audit,
independent Standards and Spec reviews and candidate verification. No chapter
or shared unit is accepted by the presence of this note.

## Source and local reuse

The manuscript is the July 27, 2026 edition of *Functional Data Structures
and Algorithms: A Proof Assistant Approach*, available from the
[official book site](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
The inspected PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Page numbers below are printed pages.

| Source claim | Location | Local observation |
| --- | --- | --- |
| Ordinary node-labelled trees and their inorder sequence | Chapter 4, pp.48–49 | Existing `Trees.inorder`, including ordered occurrences and the label-map law |
| Recursive BST invariant: whole left subtree below the root, whole right subtree above, and both child invariants | Chapter 5, p.59 | The new recursive `Trees.Ordered` specialized to `<` |
| BST equivalence with strict inorder ordering | Chapter 5, p.64 | Generic relation bridge under transitivity, then the strict-order specialization |
| Adjacent and all-later-element descriptions of strict ordering | Chapter 5, pp.64–66 | Pinned standard `List.SortedLT`, `List.Pairwise` and `List.IsChain` bridges |
| Root rotation preserves inorder | Chapter 5, pp.67 and 70 | Existing actual optional root-rotation law, followed by the new ordered-state adapter |
| Semantic map pairs are ordered by their keys | Chapter 6, pp.81–83 | Strict relation pulled back along an arbitrary key function, retaining full payload inorder |
| An annotation can be observed through its logical payload | Chapter 4, pp.56–57; Chapter 5, p.71 | Existing `Cached.erase` and exact erased-inorder laws, independent of `Cached.Valid` |

The supporting Isabelle source is pinned to mirror commit
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. This is an inspected supporting
revision, not an assertion that it generated the evolving manuscript.
The relevant primary files are:

- [Tree.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Tree.thy):
  `bst_wrt`, relation weakening, inorder membership, strict/weak BST equivalences.
- [Sorted_Less.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorted_Less.thy):
  the strict-order convention and adjacent/list decomposition laws.
- [Tree_Set.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Set.thy):
  later consumers of the strict inorder invariant.
- [Tree_Map.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Map.thy)
  and [AList_Upd_Del.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/AList_Upd_Del.thy):
  full key/value inorder and strict ordering of its mapped keys.
- [Tree_Rotations.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Rotations.thy):
  root-operation source context; the existing local XT06 note records the
  explicit Option treatment of unmatched shapes and the wider pending scope.

The corresponding retained source SHA-256 identities are `1060e49b…61af9`
for Tree, `97119940…2d5` for Sorted_Less, `f5f9d884…65c9b` for Tree_Set,
`c6da2fe6…da43` for Tree_Map, `42f60340…f9a` for AList_Upd_Del and
`74506439…75eea` for Tree_Rotations. The complete identities and precise
read scopes are preserved in the local source preflight and checkpoint.
The applicable Isabelle notice is reproduced below.

The implementation reuses `Applications.Trees.Observations` and the exact
root/erased-inorder results from `Rotations` and `CachedRotations`. It does
not change those operations or their existing clients. The core ordering
module imports ordinary observations and standard list/order mathematics;
rotation consequences live in a separate adapter module.

## Structural order and the cross-subtree comparison

`Trees.Ordered R` is a recursive proposition. The empty tree is valid. A node
requires valid children, `R x a` for every left-subtree label x, and `R a y`
for every right-subtree label y. Its bounds range over the existing inorder
lists, whose nil/node equations enumerate precisely the source's subtree
contents. This demands whole-subtree bounds, not just child-root comparisons.
No equality decision, inhabitant, finite payload carrier or relation law is
needed to define it.

Pairwise R on the whole inorder list implies the recursive invariant for any
relation R. The reverse direction additionally needs comparisons between
every left label and every right label. Transitivity supplies them through
the root. Under that explicit premise, the two properties are equivalent,
and exact equality of two inorder lists transports and reflects the recursive
invariant. Transitivity is a uniform sufficient law for this bridge; it is
not asserted to be a necessary characterization for each individual tree.

The successor relation on natural labels shows the boundary. Let `R a b`
mean `b = a + 1`, with a tree rooted at 1 and singleton children 0 and 2.
Its recursive bounds hold, but `[0,1,2]` is not pairwise R because R 0 2 is
false. Its legal left rotation puts both 0 and 1 below root 2 and loses the
recursive invariant. Inorder remains exactly unchanged. The connected
examples retain all of these observations on the actual tree and rotation.

Relation implication transports the recursive predicate without transitivity.
Similarly, mapping labels has an exact pullback law for arbitrary relations:
ordering a mapped tree by S is equivalent to ordering the original by
`fun a b => S (f a) (f b)`. No injectivity is needed for that correspondence.
Forward relation preservation is separate from reflection; neither an
arbitrary injective map nor a merely one-way relation law gives an order iff.

## Strict keys and the book's sortedness convention

For `key : α → κ`, the strict key relation is `key a < key b`. A preorder on
keys supplies the transitivity and irreflexivity used here. Payloads acquire
no order, equality decision or default, and key is not assumed globally
injective. The ordered-tree predicate is equivalent to strict pairwise order
of the mapped key inorder, and hence to the standard `SortedLT` observation.
The standard `SortedLT`/`IsChain` bridge connects this with the manuscript's
adjacent-element formulation without defining another sorting predicate.

Strict ordering yields `Nodup` of the mapped **keys**. Existing list results
then give payload distinctness and injectivity of key on this actual tree's
support. These are derived local consequences, not assumptions about every
possible payload in the carrier.

Over a partial order on keys, the standard list theorem gives the converse
characterization by nondecreasing keys and distinct keys. Antisymmetry stays
explicit. In an indiscrete preorder on two unequal elements, a list can be
nondecreasing and have no repetitions while failing strict order. This is
why the earlier preorder domain cannot silently be copied onto the converse.

Two other distinctions remain visible in the cases:

- Repeated labels such as the existing `[1,1,1]` rotation fixture are weakly
  ordered but fail the strict BST invariant. The source's p.54 sorted-input
  statement therefore needs strict order, or weak order with distinctness,
  for its future BST consequence. This unit does not implement the balancer.
- Full records `(1,10)` and `(1,20)` are unequal and can be increasing under
  an explicit lexicographic full-pair relation. Their mapped keys repeat 1,
  so they do not form a strict-key tree. Chapter 6's semantic values remain
  in full inorder; neither lexicographic value ordering nor cache erasure
  replaces its key invariant.

A key-preserving payload map preserves and reflects the pulled-back strict
relation even when it is globally noninjective. Erasing a Boolean payload
component while keeping its Nat key is a concrete example. A constant map
that collapses every key of a multi-node strict BST does not preserve the
invariant. Both facts are compatible with the existing unconditional
inorder-map and rotation-map equalities.

## Ordinary rotation and cached rebuilding

The ordinary adapters consume an actual equation `rotateLeft? t = some t'`
or its right counterpart. The existing inorder theorem and the transitive
ordering bridge give `Ordered R t' ↔ Ordered R t`. Empty and singleton
trees can be ordered while having no legal rotation; the adapters do not
assert existence of a successful result or reinterpret failure as identity.

The cached adapter uses the actual equality between erased inorder of the
two smart reconstructions. It needs no validity of stored fringe annotations,
no root-summary reassociation, and no balance property. Its conclusion is
ordering of erased logical payloads. The separate cache-validity laws still
require every retained fringe to be valid, and summary equality retains its
own reassociation premise.

The connected cached case uses the existing corrupted fringe, whose erased
inorder is `[0,1,2,3]`, followed by pivot labels 4 and 5 with other fringes
empty. The actual smart reconstructions both erase to inorder
`[0,1,2,3,4,5]`. Ordering is transported through the new adapter, while the
old validity equivalences expose the retained corrupt fringe in both results.
Conversely, an existing correctly annotated duplicate-labelled tree has
valid cache fields but fails strict erased ordering. These predicates remain
independent.

## Connected cases and statement assessment

`Examples.OrderedTrees` connects the generic laws to the manuscript's p.59
tree with inorder `[2,3,5,6,8,9]`, an actual legal rotation and inverse,
generic strict three-label inputs, empty/singleton domains, strict-key
distinctness, the source adjacency observation, and the qualified weak-order
characterization. It retains the relation, repeated-key, non-antisymmetric
preorder, map and cache boundaries described above. Existing tree/cache
fixtures retain their original contracts and are reused for their established
observations.

The intended statement assessment checks the actual relation direction and
transitivity scope, key versus full-payload distinctness, local order-instance
scope, independent universes, exact successful result, and the separation of
erased order from cache validity. The source drafts have complete proof text;
elaboration, import sufficiency and warning cleanliness remain unverified.
Final validation and independent review must assess the committed candidate.

## Coverage limits

This unit supports the invariant portions of local rows C05-001/025, the
ordered-state consequence of C05-043, strict-key portions of C06-044/049,
and the qualification for the later C04-058 balancing result. Partial rows
remain partial until their remaining observations and algorithms are supplied.

Exercise 5.1's all-node-triple characterization and Exercise 5.3's direct
recursive BST/set proof route remain separate. So do lookup, insertion,
deletion, split-min, joins, splitting, Set/Map refinement and interfaces,
balance and height/work bounds, interval-cache/search, positioned rotations,
schedules/counts/distance, and all later chapter obligations. The p.82 map
split-min reference correction remains in the Chapter 6 source record.

No search correctness, logarithmic height, execution tariff, allocation or
physical runtime conclusion follows merely from this semantic predicate.
The source operation and actual observation interfaces remain available for
those later proofs under their own exact hypotheses.

## Isabelle notice

The following is the pinned Isabelle `COPYRIGHT` notice, with trailing
whitespace normalized for the repository's ordinary diff checks.

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
