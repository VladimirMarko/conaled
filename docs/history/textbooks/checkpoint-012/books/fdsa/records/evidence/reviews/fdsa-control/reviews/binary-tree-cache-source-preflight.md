# Shared tree draft: retained bounded source and API assessments

Recorded 2026-11-02. Root transcribed the completed read-only assessments from
`/root/architecture` and `/root/tail_examples_preflight`. These are implementation
support for uncompiled drafts, **not either independent final-review axis**.
Neither source reading supplies elaboration, integrated validation or acceptance.

## Exact scope and inspected source identities

Requirements: `binary-tree-cache-requirements.md`, version 1, SHA-256
`81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`.
The four formal files were stable during the completed assessments:

| Path in `conaled-tree-cache` | SHA-256 |
| --- | --- |
| `Applications/Trees/Observations.lean` | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Cached.lean` | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Resources/TreeCache.lean` | `54d6bf9255e4d2b619fcd079a5636bac391aeb44eafe45cc0f4c6abfc2afebf6` |
| `Examples/TreeCache.lean` | `ae78e0f515ba11c9f5348533624df49da59d98887689a16c16a35c3f880fd754` |

The contributors did not inspect the integration/documentation being written
separately. The earlier resource reading preceded removal of a redundant
trailing `rfl`; its statements and computation did not change. The completed
API reading inspected the current proof shape listed above. No source finding
required a statement or scope change.

## Architecture and pinned-API reading

The contributor found no actionable source/API mismatch. The relevant checks
and exact interface observations were:

- The pinned `BinaryTree.node` takes label, left and right. Its node count is
  left+right+1, height is max(left,right)+1, and
  `numLeaves_eq_numNodes_succ` has the orientation used by the map proof.
- The fold's separate universe parameters and product-labelled cache carrier
  preserve independent payload and summary universes. The resource result
  lives at the tree's universe while its observation remains Nat; the nested
  existing `bind` operations permit those differing value universes.
- Fusion and cache validity use the supplied operation laws. Erasure and
  shape statements are unconditional. `smartNode_valid_iff` retains both
  child premises, and `annotate` computes an actual cached tree through the
  ordinary fold, with erasure, validity and root agreement separate.
- `OrderedSummary` has `summary_nil`, `summary_append` and
  `summary_singleton`, but no `summary_cons`. The draft correctly rewrites a
  cons as a singleton append. The two append laws give
  `summary l * (measure a * summary r)`; the draft's reversed `mul_assoc`
  has precisely the direction required for its left-associated target.
- The concrete word result is definitionally the displayed concatenated word
  under pinned `FreeMonoid.of`, `ofList` and multiplication. Its derivation
  first invokes the public ordered-summary composition; no commutativity or
  new summary framework is introduced.
- `CallCount.arguments_rule` exposes both argument observations and the
  callback observation at their returned values. `tick_cost` adds one.
  The constructor actually performs those two reads and stores the callback's
  returned value. Its exact count has no validity or value-correctness premise.
- The callback hypotheses name exactly the reached call. Using the existing
  `bind_erases` would instead require a global callback contract; the direct
  proof appropriately avoids that strengthening.
- Existing `appendRun_exact` supplies `(xs ++ ys, xs.length+1)`. The list
  callback and n+4 family use this actual computation, with annotation/read
  laws and `inorder_length` connecting the length to actual valid tree inputs.
- `BinaryTree.left` and `.right` are present as total simp-enabled operations
  at the pin. The malformed-cache clients therefore use supported operations.
  The `Empty × beta` and generic erased-fold cases add no default-label or
  same-universe premise.

The contributor explicitly left mechanical elaboration and simplifier behavior
to the required project gate. No compiler/checker was run to infer a pass.

## Independent mathematical/client reading

The second contributor found no concrete semantic, callback-premise,
constructor-order, cost or public-connection error in the stable formal drafts.
The completed assessments cover the core/resource files and then the examples:

- The fold uses left-summary/label/right-summary consistently. Generic
  statements require no payload order/equality decision, monoid,
  commutativity or inhabited-type premise.
- The canonical size/height observations remain the existing ones. Inorder
  preserves occurrence order. The map/erasure laws include noninjective maps
  and invalid annotations.
- Recursive validity is not replaced by a root-only test. The central cached
  result compares against the independent erased structural fold, and the
  annotation operation computes its stored values rather than assuming them.
- Expanding the measured construction gives
  `1 + (1 + (c + 0)) + 1 = c+3`. Here c belongs to the actual reached callback.
  Valid children and callback value correctness appear only in their own
  semantic conclusions. The local bound assumes only c<=K.
- The arbitrary-payload size/height readers consume the generic validity,
  canonical fold and erasure laws; height correctness has no balance premise.
  The asymmetric annotation gives size 4 and height 3 through those results.
- Both pair projections explicitly invoke fold fusion, and the pair-reader
  theorem uses one pair-validity premise to recover both observations.
- The arbitrary-monoid sequence composition retains left/node/right
  multiplication order. The concrete FreeMonoid word follows through this
  public composition and the fixture's inorder result.
- The repeated-label map retains four occurrences and the expected shape.
  The balanced/chain example separates inorder from height. Empty-label
  cases retain the supplied summary base without inventing a payload.
- The corrupted four-node tree has stored root 4, true size 4 and local
  root equation 4=2+1+1, yet invalid descendants. Its smart-constructor
  counterexample consumes the public validity equivalence and reconstructs
  the same corrupt tree. Erased-fold transport also covers arbitrary
  annotations independently of their validity.
- Zero-observation size/height callbacks give local cost 3 through the
  public count theorem. Their value/cache correctness uses both pure and
  measured contracts, with child validity separate from cost.
- The actual append callback contributes length+1. The valid repeated-label
  chain is constructed with `annotate`; its read length is n, and the local
  result is the next annotated chain. The observed local work is n+4,
  including 4 at n=0. Its unbounded-cost statement follows from that same
  valid family. Preparing those cached inputs is explicitly outside this
  local observation.

## Limits

No contributor wrote or modified a file or performed a compiler, checker,
project hash helper, enumeration, Git/ref, cache/configuration, gate or remote
operation for these assessments. Root retained their responses here.

Documentation, public-root integration, the clean immutable candidate identity,
focused compilation, complete candidate build/source guards/exhaustive audit,
and both independent final review axes remain separate obligations. The
current old Chapter 1 gate continues unchanged. None of the source preflights
closes FDSA-XT01, Chapter 1 or any later source obligation.
