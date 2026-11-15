# FDSA-XU06 stopped-source assessments

Status: bounded source assessments of an uncompiled draft; neither final
Standards nor final Spec review, no acceptance credit. Chapter 1 and every
shared unit remain unaccepted. Old gate 80227 is unchanged.

Frozen requirements: permutation-placement-requirements.md, SHA-256
1769c0550a448d9a5de06b4e926006318723887397f65d4dfabf687bdbef6902.
Fixed source base: a5341221bd3e28d76e3b8ad2bc1683a74621ad5e.
Core reading identities are in permutation-placement-core-source-snapshot.json.

## Order source handoff and root reading

The architecture contributor authored only the existing Order module's new
invariant-event section, a direct ENNReal.Inv import and module-description
paragraph. The stopped source has 35,628 bytes / 709 lines, SHA-256
f0b6ee804b5a972f151858b7e69c87730fc7aea284f245deef725cf288e1ef03.

The new private inter_fiber_mass_eq reuses the original set-preserving witness
and right multiplication π ↦ π * σ.symm. The E component uses hInvariant;
the order component uses mapped-list injectivity. The bijection preserves
the finite count measure and uniform normalization.

The public uniformOn_inter_restrictedOrder_eq has the exact frozen call
order and assumptions. Its finite partition runs under μ0.restrict E,
so its total is μ0 E. ENNReal.eq_div_iff cancels the finite nonzero factorial,
never the event mass. Unsupported lists have empty slices. No target-list
measurability, event positivity, separate event measurability, public finite
enumeration, inhabited key or nonempty subset is introduced.

The contributor reported no statement mismatch and compared the preceding
source block with the old joint checkout: after removing only the new
section/import/header paragraph it was byte-identical. Root independently
read the full new section and changed header/import and found no concrete
source issue. This does not certify elaboration or final approval.

## Independent bounded reading of the root-owned count and placement sources

The architecture contributor then read both complete stopped root-owned files
and the frozen requirements. Root did not edit those files during the read.
The inspected identities, subsequently captured without a project hash helper:

| File | Bytes / lines | SHA-256 |
| --- | --- | --- |
| Applications/Probability/PermutationExpectation.lean | 14,267 / 303 | 86210864ee226d247f5ac16df34679651376cf2c14d77127ceb7468f8b91f24d |
| Applications/Probability/PermutationPlacement.lean | 14,329 / 259 | c7511e4d14886733f3d19c0fbbb97e8ce3ba56a2e7bd341d43da47066a97f9c8 |

Result: **no concrete source finding**. The assessor recorded these reasons:

- The deterministic counted-set identity uses σ.symm in the correct inverse
  direction, reindexes both membership implications and keeps only LT P.
  It preserves the Set.ncard infinite-set convention. The new declaration
  does not claim pointwise preservation of a named outsider.
- Canonical independence sums the actual E-sliced fibers over supported
  orders in an arbitrary target event. The restriction calculation uses the
  actual count event and the same order observation.
- The generic theorem transports the joint event and both marginals through
  HasLaw.measure_eq on finite target events. It adds neither finite Ω nor
  stronger measurability of Π and requires no list singleton class.
- Scalar weighted laws use only a local discrete list measurable space.
  Natural subtraction occurs before casting, and the explicit mean retains
  injective linear priorities.
- The private real-moment conjunction proves integrability of the count,
  actual order weight and product on the finite target, then transports all
  three to the actual environment before extracting the public identity.
- The pertinent pinned HasLaw, IndepFun, restriction and integration
  declarations were read; their invocation orders match the written proof
  shapes. No elaboration result is inferred from that inspection.

The reading hold was released after this report. These exact bytes remain
the current core until a separately recorded correction changes them.

## Bounded documentation assessment before completed-case matching

The architecture contributor read the complete new source-use note, appended
XU06 reconstruction-map section and the two new public root imports against
the full frozen requirements and stopped cores. Result: no concrete discrepancy.

The assessment specifically confirmed signed real weights with transported
integrability versus infinite ENNReal weights; raw LT versus the lawful
outside-count interpretation; both conditioning directions and their different
preserved observations; full-global HasLaw versus an internal-order marginal;
and the retained treap/C10-117 and Chapter 2 boundaries.

The exact new root imports are Examples.PermutationPlacement and
Examples.PermutationPlacementBoundary. At this phase the example prose was
treated as the frozen target. Its matching to completed stopped example sources
remains a separate pending read. No file was changed by the assessor, and this
source-only assessment is not final review.

## Main and boundary author handoffs

Both example authors read the complete frozen requirements and stopped their
assigned files before independent readings. Main: 20,213 bytes / 466 lines,
SHA-256 2c4416a41aa60ad1569fd1a9a876d1f12a55d678dc702013ca43b9c4bd9f0da7.
Initial boundary: 18,923 bytes / 404 lines, SHA-256
e159483b9af4503c4097abb469f869c26e7555bc73e6fc9b509cc55a2e4f7d86.
All eight stopped source/documentation identities are captured in
permutation-placement-source-preflight-snapshot.json.

Root read both example files completely. They use the actual old observation
fixtures, the exact new public calls, genuine finite-target integration and
the two different current conditional measures. The main author supplies the
four actual joint cells, positive/signed/ENNReal weights, true ordinal bridge,
coefficient-bound use, null events and placement-weight failure. The boundary
author supplies the actual two-atom marginal-law counterexample, generic
environment/integrability use, minimal LT and empty/full/tied cases and old
global-head/adaptive limits. No mathematical mismatch was identified by the
authors or root; the independent source readings remain separately recorded.

## XU06-BC01 — rank-alias mismatch in a rewrite

State: source finding retained; correction not yet implemented at this entry.
Severity: predicted elaboration blocker. This is not an observed compiler
failure and does not change the frozen mathematical statement.

The independent boundary reader identified a concrete rewrite mismatch in
full_infinite_product_value. Its goal uses the opened
Examples.PermutationExpectation.rank3, while the direct rewrite with
PermutationExpectationBoundary.full_subset_count has the separately defined
Examples.PermutationExpectationBoundary.rank3. These ordinary aliases agree
at default definitional transparency, but a reducible-transparency rewrite
need not unfold them to match.

Suggested correction: first bind the old result to a hypothesis with the
goal's exact priority type:

    have hzero : beforeCount rank3 (Finset.univ : Finset (Fin 3)) π = 0 :=
      PermutationExpectationBoundary.full_subset_count π

Then rewrite with hzero and simplify the actual ENNReal zero product.
The typed application preserves the earlier theorem and the required new
weighted-law client; it changes only a proof step.

Before any correction, the complete original boundary file was saved as
permutation-placement-preflight-snapshots/XU06-BC01-PermutationPlacementBoundary.lean,
with its exact path/size/hash record in XU06-BC01-identity.json alongside it.
Its identity is the initial boundary identity above. The reader continues
against these stopped bytes; no implementation change is released until
that full reading stops.

## Independent complete main-client reading

The architecture contributor read all 466 lines / 20,213 bytes of the stopped
main client, the complete requirements, current cores and pertinent pinned
indicator-integral, complement, factorial and conditional APIs. Result:
**no XU06-MC finding**.

- The actual bounded count is identified with its indicator; the retained
  ENNReal mean supplies mass 1/3, and complementation supplies mass 2/3.
- All four cells go through count_order_slice, the new invariant-event theorem
  and beforeCount_relabel. The existing marginal order law is used only for
  the marginal probabilities, not as an assumed joint law.
- Independence comes from the new full-global HasLaw theorem with HasLaw.id.
  The later event-factorization calculation consumes that actual conclusion.
- Both weighted public interfaces are used for 7/6. The Real-to-ENNReal
  weight-mean conversion supplies integrability and nonnegativity.
- The ordinal product uses the original finite-image minimum value bridge
  before integrating to 14/3. The negative-weight case directly invokes the
  real theorem, and the coefficient increase is justified by nonnegative
  expected weight.
- The two conditional directions use their own measures; both measures are
  explicitly proved different from the original global law. The count-one
  mean is genuinely integrable under the normalized changed measure.
- Null, impossible and unsupported events give zero conditional measures,
  without unsupported probability normalization.
- The actual placement-dependent weight gives product mean 1/3 versus
  marginal product 1/9, retaining the order-only-weight boundary.

The assessor confirmed that the main-client narrative matches the actual
written derivations. Boundary matching remains with its separate reading.
No edits or formal validation were performed.

## Independent complete boundary reading and XU06-BC02

The main-client author independently read the entire stopped boundary file
(18,923 bytes / 404 lines), the complete requirements and relevant pinned
APIs. Reading is now stopped. XU06-BC01 above is confirmed as a source-predicted
rewrite problem, not an observed compiler error.

XU06-BC02 is a second concrete source finding: the new direct import
Mathlib.MeasureTheory.Measure.Dirac targets a module explicitly marked
deprecated_module (since := "2026-08-20") at the pinned Mathlib revision.
Mathlib.MeasureTheory.Measure.Dirac.Def contains the used dirac and
dirac_apply definitions. Root separately read that umbrella and declaration
locations and confirmed this evidence. Severity: narrow dependency/API
cleanup; no import warning or failed build was observed. State: correction
not yet implemented at this entry.

Both findings concern the same original boundary bytes already saved for
BC01. XU06-BC02-identity.json points to that complete retained snapshot;
no original file is overwritten. The intended correction is to use the
current direct Dirac.Def import and the typed hzero proof step for BC01.

No additional mathematical or hypothesis-scope finding emerged:

- The literal half-dirac mixture observes the real identity and swap-0-2
  permutations. The map calculation establishes the uniform nonconstant
  order marginal; the independently computed joint cell 1/2 versus product
  1/4 proves nonindependence. Rejecting a full-global HasLaw via the new
  theorem then uses that established contradiction in the correct direction.
- The arbitrary-environment case transports actual product integrability
  from the finite target with HasLaw.integrable_comp and retains only the
  declared current law, without finite Ω or stronger measurability.
- The locally scoped always-true LT case has full-set count 2 and acquires
  no lawful outside-count meaning. The distinct tied-Nat case preserves
  independence while refuting the injected-priority mean substitution.
- The full-set infinite-weight statements retain the actual zero product
  and genuinely infinite weight integral, with no invalid real conversion.
- Empty/singleton cases retain normalization and the rank value bridge.
  The Fin4 outsider swap really moves a named key, while the aggregate
  preservation uses the new law with the correct inverse orientation.
- Old global-head and adaptive boundaries are accurately identified as
  mean-transfer boundaries, not false independence claims about a constant
  observation. The boundary file does not import the new main example file.

The original author can now make only the recorded corrections. The same
reader must recheck their exact stopped result; compiler and final review
confirmation remain pending even after such a source recheck.

## XU06-BC01/BC02 correction and retained-reader recheck

The original boundary author made only the typed hzero proof step and the
current Dirac.Def direct import, then stopped. The corrected file has
19,014 bytes / 406 lines. The original 18,923-byte file remains unchanged in
the retained snapshot.

The same independent reader compared the complete current file against that
snapshot and read the finding record. Its comparison showed exactly two
changes, with no theorem statement, hypothesis, definition, case or prose
change. Latest dispositions:

- XU06-BC01: implemented and source-rechecked; the explicitly typed old
  theorem now matches the goal's rank alias before rewriting. The identified
  source concern is addressed. Compiler/final-review confirmation pending.
- XU06-BC02: implemented and source-rechecked; the new direct import is the
  current defining module that supplies the used Dirac declarations. The
  deprecated direct umbrella import is removed. Final confirmation pending.

The reader also read the complete current source-use note and the new map
section against the actual boundary source. Bare LT, signed versus infinite
weights, both conditional directions, global versus marginal law, actual
two-atom counterexample, arbitrary-Ω integrability and retained old boundaries
all match. The uncompiled/unaccepted and algorithm/history limits remain
explicit. Root independently read the two corrected source locations.
No compiler or final review gate was run or credited.

## Remaining reading and validation

All core, main/boundary and documentation source readings are complete and
stopped. The two boundary findings have the implemented/source-rechecked
dispositions above, while their matching formal/final confirmation remains
pending. Original-byte evidence and complete prior entries are retained.

No compiler, full checker, project hash helper, proof audit, candidate success
record or final review has run for XU06. Focused compilation, complete matching
candidate validation, both independent final axes, immediate verification
and accepted-predecessor integration remain mandatory.
