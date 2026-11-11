# Labelled Schreier paths and action arrows

Issue [#465](https://github.com/VladimirMarko/conaled/issues/465) connects
Mathlib's symmetrified Schreier paths to its action category through the
existing shared map interfaces. The entrypoints are
[`Schreier.lean`](../../Applications/GroupActions/Schreier.lean),
[`Equivariant.lean`](../../Applications/GroupActions/Equivariant.lean), and
[checked clients](../../Examples/Schreier.lean). The
[Visual Algebra assessment](visual-algebra-assessment.md) gives the motivation.

For a left action, traversing `g` and then `h` has label `h * g`.
`chronologicalPath` reverses the chronological list before calling Mathlib's
`pathFromWord`, which traverses the tail first. `label_pathFromWord` and
`label_chronologicalPath` prove the comparison with `evalWord` for arbitrary
words, including inverse generators. This adapts a chronological list to the
left action; it does not identify left and right actions. Macauley's
right-multiplication convention reads factors chronologically left to right.

Three equalities have different contracts. Literal path equality retains each
traversal. `semanticEquiv` is the relation induced by the shared `RawMap` into
equality of action arrows, retaining the evaluated group label at fixed
endpoints. Endpoint equality alone loses stabilizer information.
`raw_paths_distinct_but_semantically_equal` exhibits a forward/backward path
that is semantically an identity but is not an empty path.
`trivial_labels_distinct` exhibits parallel loops that are semantically unequal.

The native functor supplies identity and composition preservation.
`rawMap_laws` exposes those laws for literal equality; `semantic_laws` exposes
them for the induced relation. `reflects_semantics` reflects only that induced
relation. It does not establish injectivity on raw paths. Reversal interprets
as the action group's inverse through `interpretation_reverse`; no raw-path
groupoid instance is installed.

`equivariantPaths` takes a group homomorphism, an equivariant vertex map, and
a compatible map of generator indices. It preserves raw identity and
composition. `interpretation_equivariant` is a native functor equality with
`Orbifolds.actionFunctor`. `twiceChanged` composes the shared interpretation
with two action functors through `RawMap.comp`; its laws use `comp_laws`.
`twiceChanged_comp` preserves a composite path using those shared laws.
`twiceChanged_agrees` identifies that client with changing the path twice
before interpretation, using the public equivariant label theorem.

The generic algebra lives under `Applications/GroupActions`; its equivariant
module imports the existing algebraic `Orbifolds.Equivariant` module, which has
no smooth-geometry dependency. No existing orbit, stabilizer, or smooth
consumer was changed. The action-functor bridge inherits its existing common
universe for the vertex types. It makes no finiteness assumption.

## Coverage and retained cases

`reachable_iff` reuses Mathlib's generated-subgroup orbit theorem.
`label_coverage` retains a chosen group label, and `arrow_coverage` gives every
parallel action arrow a raw path when the generators generate the whole
group. These are existence theorems, without canonical word choice, raw
uniqueness, a presentation congruence, or a word-problem algorithm. A quotient
equivalence is outside this implementation.

The finite examples all use `S3 = Equiv.Perm (Fin 3)` with transpositions
`a = (01)` and `b = (12)`:

- The regular action is a Cayley instance with trivial stabilizers.
- The natural action on `Fin 3` is nonfree: `a` fixes `2` but remains a
  nonidentity arrow there.
- The chronological path `a`, then `b`, takes `0` to `2`; Mathlib's written
  word `[a, b]` takes `0` to `1`.
- The trivial action on `Unit` retains distinct stabilizer labels at its sole
  vertex. A two-edge cancellation loop differs from the empty raw path.
- Empty generators give the trivial subgroup. The nonempty generator family
  containing only `a` also fails to reach `b` from the identity in the regular
  action: all its generated elements fix `2`, while `b` moves `2`.
- The full generator family `id : S3 → S3` satisfies generation and exercises
  both full reachability and arrow coverage.
- The composed shared client maps the regular action to the natural action by
  evaluation at `0`, then to the trivial action. Both changes preserve group
  labels while collapsing different vertex information. Its composition and
  agreement claims consume the public shared-map laws and bridge theorems.

## Declaration provenance

Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`
(`v4.35.0` in `lake-manifest.json`). The declarations below adapt or consume
that actual source; they do not reconstruct theorems from a textbook picture.

| Local declarations | Source and contribution |
|---|---|
| `Vertices`, `PathCategory` | Mathlib `Quiver.SchreierGraph`, `Symmetrify`, `CategoryTheory.Paths`; aliases only |
| `edgeInterpretation`, `interpretation` | Labelled subtype edges from `Combinatorics/Quiver/Schreier.lean`; Mathlib `ActionCategory` and `Paths.lift`; local bridge retaining forward/inverse labels |
| `rawMap`, `rawMap_laws`, `semanticEquiv`, `semantic_laws`, `reflects_semantics` | Existing `SquareKit.RawMap.ofFunctor`, `ofFunctor_laws`, `induced`, `inducedLaws`, `induced_reflects`; no parallel map hierarchy |
| `label`, `label_nil`, both `label_cons_*`, `label_comp`, `label_cast`, `semantic_iff_label` | Action-arrow label projection, native functor composition and elements-hom extensionality; local observation lemmas |
| `label_pathFromWord`, `chronologicalPath`, `label_chronologicalPath` | Pinned `SchreierGraph.pathFromWord`/`evalWord` definitions and their tail-first convention; local comparison and adapter |
| `label_reverse`, `interpretation_reverse` | Mathlib `Quiver.Path.reverse` and action-groupoid inversion; local compatibility proofs |
| `reachable_iff`, `reachable_iff_full` | Pinned `SchreierGraph.reachable_iff`; explicit generation specialization |
| `label_coverage`, `arrow_coverage` | Pinned `exists_evalWord_of_mem_closure` plus the local word comparison; label-preserving existence and full-generation arrow coverage |
| `equivariantEdges`, `equivariantPaths`, `equivariant_label`, `interpretation_equivariant` | Mathlib `Prefunctor.symmetrify`/`mapPath`, existing `Orbifolds.actionFunctor`; local generator compatibility and commuting diagram |
| `equivariantPaths_id`, `equivariantPaths_comp` | Local strict path functor identity/composition for compatible changes |
| `twiceChanged`, `twiceChanged_laws`, `twiceChanged_comp`, `twiceChanged_agrees` | Existing shared map composition and preservation laws; local public composed client and agreement |
| `SchreierExamples` declarations | New specializations and separating cases above; Mathlib permutations, stabilizers, and subgroup closure supply the algebra |

Statement review checks the arrow label as well as endpoints, the reversed
multiplication convention, the direction of equivariance, the explicit
generation assumptions, and the distinction between literal and induced
relations. The negative cases establish failed consequences, rather than
merely recording unsuccessful proof attempts. Focused builds check these
modules; repository acceptance additionally requires the full build, exhaustive
proof audit, and independent Standards and Spec reviews.
