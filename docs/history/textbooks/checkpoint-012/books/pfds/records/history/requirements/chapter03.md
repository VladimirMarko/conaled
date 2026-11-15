# Chapter3 implementation requirements — version1, preparation only

Source: the user's complete book/thesis union in REQUEST.md and
REQUEST-union-v2.md. This records the complete intended chapter scope before
implementation. Chapter2 remains unaccepted; this document does not activate
Chapter3, select an implementation/review base or advance any coverage item.
After Chapter2's exact acceptance, record its integrated tip as the starting
base and assign the first vertical slice. Retain the full chapter scope through
all later slices and prerequisite integration.

Primary source inventory: research/chapter03-union-inventory.md, covering book
printed pp17–30, Figures3.1–3.6, Exercises3.1–3.10 and all subparts. The source
book SHA256 is b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
Thesis correspondence: Definition6.2 p64, Figures6.2(b)/6.3(b) p65,
section6.2.2 pp68,70–73, Figures6.7/6.8. Thesis SHA256 is
f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
The primary inventory retains visual inspection and source-equation comparison;
raw text extraction is insufficient for the non-strict rank comparison and
floor/ceiling notation. Later thesis tree families remain under their mapped
later chapter/supplemental owners.

## Ordinary heap interface and baseline leftist slice

- B3-HEAP/B3-HEAP-ORDER: all six operations empty, isEmpty, insert, merge,
  findMin and deleteMin. Preserve every repeated occurrence and observable
  empty failure. A common comparison structure governs heaps being merged.
  All descendants satisfy the root's heap order. Separate operations, validity,
  independent contents, selected minimum and resource assumptions. Minimum
  observation and deletion must agree on the selected occurrence even when
  distinct payloads have tied priorities. A stored optional value is not an
  empty-heap failure.
- Reuse Search.LeftistQueue and ExactPriority. The latter's exact-occurrence
  contract is the existing foundation; its explicit keyed weakening is not a
  substitute. Add only the missing meld, direct peek and empty-test capabilities
  and separate laws, with a checked ExactQueue connection. Retain the existing
  generic clients and a genuinely independent list realization. Preserve
  payload/priority generality and total-preorder assumptions where sufficient.
- B3-LEFTIST/B3-LEFTIST-OPS: cached ranks are correct; the left rank is at least
  the right rank at every node. Source makeT retains child order when ranks tie
  and swaps only when necessary. The actual merge descends the chosen right
  spine and chooses the first root on a non-strict priority tie. Establish
  content, rank and heap-order preservation. Insertion merges a direct singleton
  first; findMin inspects the root directly; deletion merges the children.
  Relate the source one-element carrier to the existing general payload/priority
  implementation rather than adding a redundant competing tree datatype.
- B3-E3.1: cached rank equals both the right-spine node count and shortest path
  to empty, and rank <= floor(log2(n+1)), including the empty case. Reuse the
  existing rank_paths/rank_size/rank_log theorems under their actual Ranked
  premises. Heap order alone must not justify a forged cached rank.
- The stated logarithmic merge/insert/delete and constant findMin costs need
  actual measured source recurrences and erasures to those operations, with
  explicit costs for priority comparison, rank access/arithmetic, dispatch and
  construction. Keep modeled operations distinct from host runtime/allocation.
  Bound merge comparisons first by the sum of the two valid ranks, then by
  sizes; deletion depends on both child ranks, not solely the old root rank.
  Source merge's branch order must be preserved if individual tests are observed;
  an aggregate dispatch convention must be named if only call counts are used.

## Remaining leftist exercises

- B3-E3.2: implement direct recursive insertion, prove its valid occurrence
  behavior and source insertion correspondence, and retain appropriate measured
  bounds. A wrapper around the earlier merge is not the requested recursion.
- B3-E3.3: build singleton heaps, then repeatedly merge adjacent pairs in rounds,
  preserving an odd tail. Handle0/1inputs, termination, exact contents/validity,
  n-1merges and logarithmic rounds with explicit zero/positive conventions.
  Prove linear *total work* using size-sensitive merge bounds and the actual
  round traversal/singleton costs. Counting merges alone is insufficient;
  existing fold insertion does not discharge the exercise.
- B3-E3.4a/b: give a cached-weight invariant agreeing with unfolded size and
  left-size >= right-size at every node. Prove logarithmic right-spine length,
  then realize the full heap interface with this invariant, preserving contents,
  failures and the intended operation bounds.
- B3-E3.4c: implement one-pass top-down weight-biased merge whose child placement
  is determined using known subtree sizes before recursive return. Prove actual
  operation correspondence and the dependency distinction from bottom-up makeT.
- B3-E3.4d: formalize the stated lazy/concurrent advantage under an explicit
  demand/dependency interpretation connected to the actual heap algorithm.
  Extensional output equality does not establish earlier root availability or
  parallel speed. Reuse cross-cutting suspension/resource foundations where
  suitable; their acceptance alone proves no heap-specific demand theorem.

## Binomial heaps and the thesis variant

- B3-BINOMIAL-SHAPE: connect equal-rank linking with descending child ranks
  r-1,...,0 and prove rankr has2^r unfolded nodes. Link valid equal ranks with
  exact occurrence/order preservation. Include the rank0–3 shapes as connected
  cases. Internal child-spine length is not an assumed constant-time rank read.
- B3-BINOMIAL-FOREST: top ranks are strictly increasing with no duplicates;
  children decrease. Relate root weights to binary size and prove the relevant
  tree/rank/child bounds. Retain the size21/ranks0,2,4 source calculation.
- B3-BINOMIAL-INSERT: actual insTree carry and singleton insertion, with the
  ordering premise that makes encountered links legal, full validity/content
  laws, logarithmic worst-case cost and exactlyklinks at size2^k-1.
- B3-BINOMIAL-MERGE: the printed forest recursion, equal-rank link and insTree
  carry, with its actual coupled logarithmic cost bound. Multiplying unrelated
  logarithmic bounds to obtain log-squared work is insufficient. A backend whose
  tied-root selection differs from the source cannot be silently equated with it.
- B3-BINOMIAL-MIN: removeMinTree/getMin returns the selected minimum-root tree
  and exact remaining occurrences; book findMin projects that result. Deletion
  removes the root, reverses its descending-rank children and merges the valid
  forests. Prove empty failures and the stated operation bounds. Forest length
  alone does not bound deletion work for a single high-rank tree.
- B3-E3.5/T6-DIRECTMIN: a direct root scan without constructing a residual forest,
  matching the thesis main implementation. Prove its full result/failure and
  tie selection agree with removeMinTree projection under the needed comparator
  laws. Do not assume left-fold/right-recursive scans coincide for an arbitrary
  cyclic comparator.
- B3-E3.6: reimplement all operations with unannotated internal nodes and only
  top-level rank/tree pairs. Prove the representation relation, reconstructed
  ranks, invariants, operation behavior/failures and retained cost guarantees.
- B3-E3.7: a generic ExplicitMin construction over an arbitrary lawful heap,
  with an explicit decision whether the cached occurrence is excluded from or
  duplicated in the underlying heap. Prove all transitions and exact occurrence
  semantics, constant findMin, and inherited logarithmic costs under explicit
  primitive-operation bounds. Preserve the chosen tied occurrence consistently.

## Red-black trees

- B3-RB-INVARIANTS: strict ordered-set semantics, no red-red edges, equal black
  count on every root-to-empty path, and explicit empty/root color conventions.
  Reuse existing ordered-tree and dependency results where their actual
  assumptions fit; do not build the desired height bound into an invariant.
- B3-E3.8: maximum node depth <=2*floor(log2(n+1)), with the appropriate size,
  black-height and ordinary-height results and correct either-root-color cases.
  A red singleton rules out an unrestricted depth<=2*blackHeight shortcut.
- B3-RB-MEMBER: color-insensitive source membership, its connection to the
  existing ordered search, actual comparison/visit count and logarithmic bound.
- B3-RB-INSERT: red-leaf insertion, the allowed temporary violation, all four
  black-red-red rotations with the four surrounding subtrees/inorder retained,
  and final blackening of the nonempty root. Prove ordering, exact unchanged or
  add-one set content, balance invariants, termination/nonempty ins and source
  representative behavior. Dependency insertion that replaces a cmp.eq value
  or leaves a singleton root red needs an explicit valid adaptation; comparator
  transitivity alone does not imply faithful value equality.
- B3-E3.9: actual linear construction from sorted duplicate-free input, exact
  contents and red-black invariants for all lengths including0and boundaries,
  with a measured linear consumer/constructor argument. Fold insertion does not
  establish the required linear bound.
- B3-E3.10a: separate left/right balancing at corresponding recursive returns,
  with valid source insertion and explicit removal of unrelated-side color tests.
- B3-E3.10b: further path-sensitive insertion that never tests off-search-path
  node colors, with the same intended validity, contents and cost guarantees.
  Observe actual tests/node identities or give an equivalent source-aware
  operational relation; equal resulting trees do not prove the test discipline.

## Persistence, context and connected applications

B3-PERSIST retains prior pure versions. Any physical cell-sharing, retained-root
or allocation claim must use an actual immutable-store interpretation: reuse
Chapter2's tools where applicable, and supply the needed two-input or rotation
refinement where a one-search-path Rebuilds law is insufficient. Self-meld
counts every unfolded occurrence even if a later realization shares cells.
B3-NOTES classifies the source's historical, compiler-portability and empirical
runtime remarks without claiming proved performance rankings or importing every
cited alternative data structure as an extra coverage milestone.

Develop meaningful applications through public laws alongside each theory.
The first slice must include empty/singleton and optional stored values,
equal-rank child order/right-heavier swapping, forged versus valid ranks,
duplicate insertion/self-meld, tied roots with distinct payloads and a
non-antisymmetric priority preorder, direct peek versus deletion work, the
fixed-root-rank deletion family, generic composition and an existing Huffman
connection. Other slices retain the discriminating cases in the source/reuse
inventories. Preserve independently justified expectations through proof fixes.

## Architecture and acceptance

Reuse conaled operations, separate laws, relational observations, resource
composition, standard asymptotics and existing concrete implementations.
Require only the hypotheses each theorem needs. Preserve universe generality
where the existing APIs provide it; use explicit transport at a shared square
boundary rather than silently specializing the carrier. Do not add an unused
generic framework, replacement evaluator or cost law assumed as an invariant.

Follow AGENTS, implement/example-driven-development and the shared review loop.
Every formal claim needs statement review and a meaningful connected use.
No new axioms, admissions, unchecked native shortcuts, proof-budget increases,
linter suppression or weakened build/audit policy. Every new module enters the
public closure and exhaustive audit. Focused compilation is development evidence.
Whole-chapter acceptance requires a clean isolated complete candidate, stock
pinned-Nix full build, exhaustive audit, matching verification record, independent
Standards and Spec on the identical complete scope, immediate final verification
and delivery of the same bytes. All local history, failed/successful evidence,
tracking and reviews enter promptly uploaded recovery checkpoints. No GitHub writes.

The first bounded assignment after activation is the HEAP/baseline-leftist/E3.1
vertical slice, as described in research/chapter03-first-slice-design.md and
chapter03-leftist-readiness.md. It is not whole-chapter completion. Continue
within the chapter through the remaining leftist, binomial and red-black items
before advancing to Chapter4. Later prerequisite integration must preserve the
recorded original chapter review base and cumulative finding history.
