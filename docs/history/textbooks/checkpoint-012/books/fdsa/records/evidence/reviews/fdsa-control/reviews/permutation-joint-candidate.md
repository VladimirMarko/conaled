# FDSA-XU05: immutable joint relative-order source draft

Recorded 2026-11-02. **Uncompiled and unaccepted.** Chapter 1 remains active;
no chapter or appendix is accepted. This handoff belongs to the existing
book implementation loop and is not either final review axis.

## Identity and preservation

- Base: `11923e9ffd17246b6f22c5594002a1ba0434e43c`.
- Candidate: `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e`.
- Worktree: `conaled-permutation-joint`.
- Branch: `work/fdsa-permutation-joint`.
- Commit: `feat(probability): formalize joint relative orders (#174)`.
- Six tracked files, 1,007 insertions and four module-description deletions;
  clean index and working tree after commit.
- Frozen requirements: `permutation-joint-requirements.md`, 14,845 bytes,
  SHA-256 `a80952af26c830231070feb9305f7c678277349c95861b39826edc9297486325`.
- Starting state and ownership: `permutation-joint-start.md`.
  Checkpoint 0023 preserves the requirements, preflights, named-case
  expectations and clean pre-code branch; receipt in `../checkpoints.json`.

The prior formal body of PermutationOrder, from its option declarations
through its last earlier proof, is byte-identical to the base. Root checked
this directly against the base Git blob in the pinned shell before committing.
Changes to that module consist of two relevant imports, an accurate module
description and the new joint-law section. No old public statement or proof
body was changed. Previous committed candidates remain preserved.

Only unchanged dependency packages are shared. No compiler or project-output
writer ran in this checkout. All preceding shared drafts and the Chapter 1
repair remain unvalidated; this candidate inherits no acceptance credit.

| Candidate file | Bytes | SHA-256 |
|---|---:|---|
| Applications/Probability/PermutationOrder.lean | 29,717 | `8a427831a044b3c2aac2b7272648ec702d8b04da2e11a1db57521dde28a0e50c` |
| Examples/PermutationJoint.lean | 13,379 | `51e712d2b69ea8abb930597452988d4fb02ec57b48503f30a18cb97287de3c28` |
| Examples/PermutationJointBoundary.lean | 11,107 | `2ed11acdb8615ae5fd9696ce9c843bf93cb59821a580229753d5b45396a7526f` |
| SquareApplications.lean | 8,464 | `556524fdf37e4237c0e086af06c97d43561b19c35886913688568ad228bdb700` |
| docs/research/fdsa-permutation-joint.md | 10,069 | `cf80730065f60325297835548c98790b14778d7db61bde84da9429c0192b4b64` |
| docs/research/fdsa-reconstruction-map.md | 21,507 | `8583097adf4bb97611ddda8b276cd5d85d7d7c1dab5bfb31685f427daa3ac408` |

## Actual joint-law construction

The core adds exactly the three frozen public results, in the existing
PermutationOrder namespace. The universal source-fiber theorem observes
the ordinary pair of two existing restrictions of the same permutation.
It retains Disjoint A B, complete Nodup positions and the earlier DecidableEq
interface. It has sample-space measurable assumptions only, with no public
finite enumeration, key order, inhabitance, list measurability, nonempty
subset or cover premise. Unsupported outcomes in either coordinate have
empty fibers and zero mass.

The private simultaneous-relabeling proof derives the exact support and
length of both lists in each supported pair. Disjointness makes the two
concatenations Nodup; the existing private list-extension helper produces
one ambient permutation. The equality is split at the justified first
length, giving both mapped lists and preservation of A and B separately.
The existing private relabeling theorem retains the orientation
π * σ.symm. Its right-multiplication bijection transports the actual pair
fibers, and counting-measure invariance makes their masses equal.

The scalar proof partitions the actual permutation sample over the product
of the two existing order supports. Their masses sum to one. The ordinary
product-finset cardinal and old order-cardinality theorem give the natural
factorial product, cast into ENNReal before inversion. Empty supports of
selected keys still have their sole empty-list order and 0!=1; Empty I
still has an identity permutation. No independent redraw is introduced.

The actual pair-map theorem adds list-space measurability and uses the
canonical product measurable space. It explicitly establishes each finite
order target as a probability measure and supplies SFinite instances before
the product singleton calculation. The target factors are evaluated through
the old actual map and scalar laws. Countable singleton extensionality and
justified ENNReal inverse multiplication give the product map equation.

A private canonical filter-pair HasLaw rewrites the existing whole-S law
through its actual global projection, composes maps, and applies both old
nested-filter equalities. The public `hasLaw_filter_pair` composes this
canonical law with the caller's existing hY. Ω can be arbitrary measurable,
μ can be a changed environment and Y need only be a.e. measurable as recorded
by HasLaw. Containment A,B⊆S and disjointness remain explicit. There is no
public permutation-space measurable premise on this generic result and no
new independence, execution, sampling or conditioning framework.

## Connected cases

The main Fin4 case reuses the earlier public experiment and fixed disjoint
sets {0,2}/{1,3}. It derives joint mass 1/4 from the new universal formula,
both marginal masses 1/2 from the old scalar theorem, and zero mass when
either coordinate is malformed. The actual new pair-map equation and old
marginal maps are assembled into HasLaws; the existing
indepFun_iff_hasLaw_prodMk_prod yields the actual IndepFun statement.

The boundary module provides a shared Fin5 fixture used by both unequal-size
and conditional examples. The proper-union case {0}/{1,2,3} leaves key 4
outside and derives mass 1/6 from the new scalar law. Its non-cover facts
are explicit. The empty/full Fin4 case records the actual inverse-order
value and scalar mass 1/24. Empty I records normalized mass one, uses the
new scalar formula and also feeds the old actual empty whole-order HasLaw
to the new generic theorem. Pointwise equality transports the filtered pair
to the actual empty pair; no key is manufactured.

For Fin3 overlap {0,1}/{1,2}, a finite supported-list table and the old
nested-filter laws identify the actual pair event ([1,0],[1,2]) with the
actual full-order first-key-1 event. The old XU03 head law gives mass 1/3;
the two old marginal laws give 1/2 each and product 1/4. The explicit
inequality refutes deleting disjointness without asserting that all
overlapping observations must be dependent.

The main Fin5 conditional case starts from the actual full-order HasLaw,
obtains head-key-2 mass 1/5 and the actual conditional-tail HasLaw through
XU03, and proves conditional normalization. The new generic pair-filter
theorem is applied under that actual changed measure for {0,1}/{3,4},
with disjointness and containment in univ.erase2 proved. Old conditional
marginals and the new joint law also give its existing IndepFun statement.

Both tail filters equal the original same-sample projections on the head
event through XU03's pointwise bridges. Conditional a.e. transport then
gives the actual projection pair the same HasLaw. Both supported-pair masses
1/4 are calculated from that product law with explicit target normalization,
not from a fresh independent experiment. The environment's head-event mass
changes from 1/5 to one, proving it differs from the original uniform law.
All calls retain the original complete positions.

## Source assessment and current validation

The core and boundary authors stopped at the exact hashes above after
bounded statement/API assessments. Root read the complete new core section,
its reused earlier machinery, both new example modules, the frozen
requirements and source-use document. No mathematical or scope mismatch
was identified in these author assessments. The main example reuses the
public Fin5 fixture by the agreed names; there is no boundary-to-main import.

The pinned-shell staged whitespace check passed before commit. The bounded
marker inspection of the three Lean files found no admissions, source axioms,
unsafe/partial declarations, native_decide or skipKernelTC. These are source
checks, not proof-term or exhaustive axiom-audit evidence.

The separate stopped-draft source assessment is complete at
`../research/permutation-joint-draft-preflight.md`, 18,972 bytes,
SHA-256 `402aee367682646edf07610d260763c3dfd5b7c498ca7d4faf0b9413ae26e726`.
It read the full core and both examples, the new document and scoped map/
import changes, and rechecked all six unchanged source hashes. No concrete
XU05-SP finding was opened. Root read the complete report. This bounded
statement/proof-route/API assessment is not final Standards or Spec approval
and supplies no compiler, audit or acceptance credit.

No focused compilation, whole-candidate check, proof audit, elaborated-type
inspection or matching success record exists for this candidate. Remaining
elaboration risks include pair/finset coercions, mapped-concatenation splitting,
instance inference, ENNReal normalization, finite-table decision, event
rewrites and HasLaw congruence. Its preceding draft dependencies remain
uncompiled as well.

## Source limits and resumption

The result supports the fixed-partition pair-law step of the selected AFP
quicksort distribution method. Conditional expectation recurrences can use
the earlier marginals without independence. Actual occurrence partitions,
pivot rank, strict/reflexive partition agreement on distinct pivot-deleted
keys, recursive program/value/cost correspondences, complete histories,
fresh-choice coupling and the book's cost tariff remain chapter work.
The two-way repeated-key behavior is not replaced by a different algorithm.

Internal disjoint relative orders do not imply independent global positions,
raw priorities, adaptive sets or overlapping operands. A mixture over revealed
pivots needs its own law. C10-117's conditional depth, Jensen, actual work and
correlated weighted charging remain open. No chapter is closed by this unit.

Keep the old Chapter 1 gate unchanged and collect its result. Validate the
repaired Chapter 1 first in the idle isolated cache; retain all correction
candidates, independent final reviews and immediate verification. Reconcile
shared drafts only under their recorded acceptance dependencies. This new
extension must then receive matching focused/full guarded validation,
exhaustive audit, both independent final axes and immediate verification.
Every old and new connected case remains in the public build/audit scope.
