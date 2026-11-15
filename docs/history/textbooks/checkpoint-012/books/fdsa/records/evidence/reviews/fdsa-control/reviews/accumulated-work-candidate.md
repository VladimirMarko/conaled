# Shared accumulated-work draft candidate

Recorded 2026-11-02. FDSA-XW01 remains unaccepted and uncompiled.

- Starting/review base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Draft commit: `7c6bc92c276d39e84351324c442869b8ffa6758c`.
- Branch: `work/fdsa-accumulated-work`.
- Development checkout: `conaled-accumulated-work`, clean after commit.
- Commit message: `feat(probability): bound accumulated random work (#174)`.
- Change: six files, 837 added lines.
- Frozen requirements: `accumulated-work-requirements.md`, SHA-256
  `85c651891cf8c8ee016706bf8baad7711dbd9965eb20ad5c6e96d2ab112728e1`.

The base is the unvalidated Chapter 1 repair. This shared unit cannot become
an accepted dependency merely because its source is committed. If Chapter 1
elaboration or final review changes that base, reconcile the branch explicitly
and capture a new candidate with matching validation before integration.

## Supplied statements and connections

The core module contains six ordinary theorems under
`Applications.Probability.AccumulatedWork`: iterated integral bounds, shifted
and total accumulated integrals, a finite-integral specialization, a
single-prefix tail theorem and its stage-cap corollary. It uses the supplied
measure and ENNReal-valued observations, existing countable sum/integral
interchange, geometric series and Markov. Operation, probability law and
observation correspondence remain external inputs. No extra probability
carrier or executor is introduced.

`Examples.AccumulatedWork` evaluates the existing measured executor under a
uniform Fin 8 environment. It proves separate ordered output and cost
equations, the actual sum-to-cost bridge, exact means and a nonempty tail.
Its public upper bounds use the generic total, finite, shifted and tail
theorems. Shared-event masses expose dependence. Actual reweighting followed
by bind retains the output and gives the affine observation `2*W+3`; its
bound uses the generic-derived work bound and existing integral linearity.

`Examples.AccumulatedWorkBoundary` connects an actual three-entry measured
program returning seven to zero-drift work. It keeps zero versus positive
shift behavior, zero-work validity for total integrals, the zero-threshold
tail failure, the missing-prefix Fin 3 counterexample, and q=1 constant work
with infinite accumulated integral. The rare-work prefix failure follows
from the public tail theorem and the positive exact tail mass.

The main example imports the boundary file, and the public application root
imports the main example. The reconstruction map and focused research note
identify the later chapter-specific sampling, execution and tariff bridges.

## Source identities

| File | SHA-256 |
|---|---|
| `Applications/Probability/AccumulatedWork.lean` | `7731f8a6c5222810ba11a056fc620c68a152dce0024ff3e2544d17fff70a80ba` |
| `Examples/AccumulatedWork.lean` | `7ef773d2ce87ce1b119838e083ee4a4cff072f5d96f4a8887f8494a80d04c20c` |
| `Examples/AccumulatedWorkBoundary.lean` | `68ba8fd9571ad860d7f5aabd7093f35c0220ff12ead1e283e903b5bdc90a6927` |
| `docs/research/fdsa-accumulated-work.md` | `191a7c449f936b84c17f3f5d33a935dd4440a199fc7287e576dfd38f4fbaca8e` |

## Author statement review

Root inspected the full final core and both example modules. The architecture
contributor wrote and source-reviewed the core and boundary file. Root wrote
the main example, documentation and public integration. This bounded delegation
extends the initial ownership plan in `accumulated-work-start.md`; it changed
no frozen mathematical requirement.

The source-reading contributor independently performed an author-side
semantic preflight of the stable main example, core and document, recorded in
`../research/accumulated-work-draft-preflight.md`, SHA-256
`b6d974317c97a4d97c32b2dd0f18b27edd08b2647cf680d40bdb7732468b5ab7`.
It found no source-level semantic/scope issue within that assigned pass. The
boundary file was expressly excluded from that pass and reviewed by root and
its author. This is preparation evidence, not either final independent axis.

The per-claim assessment retains these distinctions:

- The initial and one-step premises concern actual observations under one
  common measure. They do not assume a desired accumulated-work inequality or
  establish a conditional sampling model.
- The mean induction uses no measurability premise. Sum interchange needs
  only almost-everywhere measurability; no finite-measure or normalization
  assumption enters the core.
- ENNReal arithmetic retains infinity. Strict contraction and finite N are
  supplied exactly for finite-integral conclusions; q=0 and N=0 remain valid
  for the appropriate mean statements. No division by q occurs.
- The main tail takes only its actual prefix bound. Its proof establishes
  finite-prefix cancellation and a positive finite Markov threshold. The
  stage-cap corollary derives that prefix premise rather than strengthening
  the main contract.
- The independent Fin 8 mean is `15/8`, remaining mean `7/8`, and threshold-three
  mass `1/4`; generic bounds two, one and one-half are obtained through the
  public results. Natural residual subtraction is safe because stage zero
  always contributes one, and the finite equality covers every environment.
- The affine value is unchanged; its mean `27/4` and threshold-nine mass `1/4`
  match actual reweight/bind equations. Integral normalization is local to the
  finite probability example, where the added constant integrates to itself.
- The N=0 tail and omitted-prefix counterexamples make both hypotheses
  substantive. The q=1 client shows why a generally valid extended bound need
  not be finite. Finite total work is not advertised as finite-step termination.

No new mathematical scope issue was found in these source assessments. The
explicitly deferred algorithm-specific conditional laws, cost bridges,
quicksort two-branch analysis and treap priority/weighted-cluster arguments
remain in the chapter tickets.

## Validation and next step

`git diff --cached --check` passed on all six staged files before commit.
A bounded source-marker scan of the three new Lean files found no admission,
new-axiom, unsafe/partial or kernel-bypass marker. That scan is not the
exhaustive proof audit. No focused compiler invocation, full guarded check,
audit, axiom report, verification success record or independent final approval
exists for this candidate.

The active old Chapter 1 gate remains unchanged. Its result must first be
collected, then the repaired Chapter 1 candidate validated and reviewed in the
idle isolated checkout using ordinary Lake tracking. Preserve the sequential
acceptance boundary. Later reconcile this unit with the accepted base,
validate core/examples and the entire immutable candidate under the pinned
environment, obtain both independent review outcomes, and run final candidate
verification immediately before acceptance. Source/API inspections do not
establish elaborated types or proof terms; ordinary elaboration issues remain
possible in the draft.
