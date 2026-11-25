# Textbook machine integration and next work

This receiving integration brings the final external textbook source into the
library under [#713](https://github.com/VladimirMarko/conaled/issues/713). That
issue records the exact candidate, full receiving build/audit, matching
verification and independent Standards/Spec outcomes. Existing #659/#660
acceptance covers its original increments.
No new textbook row is qualified by the current documentation or source intake.

External authoring is retired. Use the repository's [AGENTS.md](../../AGENTS.md)
and the [four-book index](../textbooks/README.md); no external restart seed is
needed. [CTB](../textbooks/CTB.json) retains stable task IDs and complete literal
requirements, while [coverage](../textbooks/coverage.json) owns denominators.

## Source families

The [certificate paper](fdsa-rotation-certificate-preparation.md) explains raw
acceptance, attained-minimum witnesses and the observation boundaries. Follow
these entry points to definitions and connected cases:

| Mathematical task | Source and client entry points |
|---|---|
| Recognize raw trees and whole inputs, retaining exact suffixes and malformed-input bounds | [TreeParser](../../Applications/Resources/RotationCertificate/TreeParser.lean), [InputParser](../../Applications/Resources/RotationCertificate/InputParser.lean), [parsing clients](../../Examples/RotationCertificateParsing.lean). |
| Check a bounded mixed-rotation trace and select an attained-minimum certificate | [Streaming](../../Applications/Resources/RotationCertificate/Streaming.lean), [Witness](../../Applications/Resources/RotationCertificate/Witness.lean), [Verifier](../../Applications/Resources/RotationCertificate/Verifier.lean), [verification clients](../../Examples/RotationCertificateVerification.lean). |
| Preserve exact raw binary acceptance and quadratic witness size | [BitCodec](../../Applications/Resources/RotationCertificate/BitCodec.lean), [BinaryVerifier](../../Applications/Resources/RotationCertificate/BinaryVerifier.lean), [binary clients](../../Examples/RotationCertificateBinary.lean). |
| Implement finite machine stages and their cleanup/output protocol | [RotationCertificate modules](../../Applications/Resources/RotationCertificate/), culminating in [FrontEndStreamMachine](../../Applications/Resources/RotationCertificate/FrontEndStreamMachine.lean) and its [clients](../../Examples/RotationCertificateFrontEndStreamMachine.lean). |
| Pay for native stack-to-tape, tape-to-primitive and finite-control simulation | [StackToTape](../../Applications/Resources/TuringSimulation/StackToTape.lean), [TapeToPrimitive](../../Applications/Resources/TuringSimulation/TapeToPrimitive.lean), [FiniteControl](../../Applications/Resources/TuringSimulation/FiniteControl.lean), [simulation clients](../../Examples/TuringSimulation.lean). |
| Expose ordinary literal input, finite native packages and actual coordinates | [OrdinaryPackage](../../Applications/Resources/TuringSimulation/OrdinaryPackage.lean), [VisitedSpace](../../Applications/Resources/TuringSimulation/VisitedSpace.lean), [FrontEndStreamTapeMachine](../../Applications/Resources/RotationCertificate/FrontEndStreamTapeMachine.lean). |
| Decide a uniquely delimited literal input/certificate pair in polynomial time | [DelimiterMachine](../../Applications/Resources/RotationCertificate/DelimiterMachine.lean), [DelimiterTapeMachine](../../Applications/Resources/RotationCertificate/DelimiterTapeMachine.lean), [DelimiterPolynomialTime](../../Applications/Resources/RotationCertificate/DelimiterPolynomialTime.lean). |
| Relate a combined print/move decider to an explicit bounded-witness criterion | [ConventionalPolynomialDecider](../../Applications/Resources/TuringSimulation/ConventionalPolynomialDecider.lean), [ConventionalVerifier](../../Applications/Resources/TuringSimulation/ConventionalVerifier.lean), [BinaryYesVerifier](../../Applications/Resources/RotationCertificate/BinaryYesVerifier.lean), [delimiter clients](../../Examples/RotationCertificateDelimiterMachine.lean). |

Shared machine contracts retain full configurations, supplied starts and
registers, finite support, raw rejection, terminal output and actual counts.
Source-event work, native transitions, conventional print/move time, occupied
cells and visited coordinates are distinct observations. The generic
[PolynomialDecider](../../Applications/Resources/TuringSimulation/PolynomialDecider.lean)
and [PrintMove](../../Applications/Resources/TuringSimulation/PrintMove.lean)
own their contracts independently of rotation certificates.

## Receiving module layout

The receiving split retains every original public import path and declaration
name. Ten large machine/example files now delegate to 65 modules; the simulation
example delegates to eight more. Existing imports therefore continue to select
the same public contracts. The exact original files remain in the preserved
source delta for comparison.

| Entry point | Module boundaries |
|---|---|
| `FrontEndMachine` | Transport, finite syntax, execution, prefixes and packages. |
| `PositionedRotationMachine`, `MoveApplyMachine` | Primitive syntax and execution, represented source inputs, physical potential/space, packages and installation. |
| `StreamMachine` | Core evaluator, actual runs, physical bounds, frontend compatibility, packages, initialized/clean execution and installation. |
| `FrontEndStreamMachine` | Physical stores, arbitrary component execution and potential, prefixes, complete execution, packages and installation. |
| `DelimiterExecution` | Raw protocol classification, actual preprocessing loops and composition. |
| Large machine examples | Literal configurations, trace edges and bounds, source connections, packages and installation cases. |
| `Examples.TuringSimulation` | Stack-to-tape, primitive/reflection, finite control, ordinary input, visited space, ordinary packages and print/move clients; polynomial normal forms have their own example module. |

These boundaries follow differing hypotheses and observations. They preserve
full stores, malformed inputs, first-owned-boundary restrictions and separate
source and machine costs. Public identifiers retain their existing mathematical
and Mathlib spellings, including `TM2`, `TM0` and `EvalsToInTime`. No delivery
number is introduced into a public name. Generic machine transport remains
under `FrontEndMachine.Transport` for compatibility; its possible extraction
belongs to a later shared-interface assessment under #658, coordinated with
#235. The existing clients already share that transport.

Native and conventional visited-space traces also have distinct command and
terminal observations. A future shared construction must recover both original
contracts, including write excursions and the final decision move. Finite
control existence remains distinct from executable transition-table export.

## Bounded next work

Each row names a deliverable and its dependency. They refine CTB-24 without
turning its current state into a chronological diary. A task is complete only
when its stated contract, connected cases and required checks pass.

| Deliverable | Dependency and acceptance boundary |
|---|---|
| Receiving acceptance evidence | #713 owns the exact-candidate full build/audit, matching verification and independent review record. Historical ST-V001/SP-V001 retain their donor status; successful receiving evidence resolves the missing whole-validation requirement for the received source, without changing historical UNKNOWN outcomes. |
| Further module and shared-interface improvements | The receiving layout above preserves existing imports and names. Assess remaining large parser modules and possible generic transport/trace extraction under #658/#235 using checked recovery of current contracts. No blanket rename or migration is implied. |
| Stationary normal-dispatch command and suffix composition | Start with the [uncompiled draft and frozen expectations](../history/textbooks/handover-2026-11-25/received/current/research/space155/next/README.md). Prove the actual self-write, one-step complete endpoint and unchanged coordinate; preserve register-dependent branches and the subsequent outer-none distinction. |
| Actual-path internal-height predicate and reserve corollary | Start with the [uncompiled height draft](../history/textbooks/handover-2026-11-25/received/current/research/height156/README.md). Preserve the selected-path quantifiers, loaded-register branches, old/new heights, unrelated-track counterexample and the stronger sufficient reserve. This alone proves no target-space bound. |
| Marked-simulator local shuttles and whole-run height bound | Follow the [geometry plan](../history/textbooks/handover-2026-11-25/received/current/research/space154/PLAN.md). Construct actual command-coordinate traces and one compatible timing/geometry witness; preserve the marker and all tracks. Then compose to the proposed `[-1,H]` interval and `H+2` visited span. |
| Finite-control and ordinary/conventional coordinate transport | Finite restriction needs command preservation, not only equal tapes or endpoints. Reflection, delimiter preprocessing and combined print/move writes have their own coordinates and temporary excursions. State and prove each transport separately. |
| Complete FDSA-5-93 computational-model/NP correspondence | Review the canonical source requirement against the explicit conventional verifier criterion. Prove the missing correspondence to an independent nondeterministic model if needed for that claim; do not rename the existing criterion to imply it. Executable indexed transition-table export is a separate capability, not supplied by noncomputable finite existence. |
| Eventual exact rotation diameter | Continue [FDSA-5-92 preparation](fdsa-rotation-diameter-preparation.md), including the primary figure-defined family, lower-bound recurrence, literal Q10/Q11 cases and tree/diagonal recovery. The certificate construction does not discharge this obligation. |

The retained source-derived space target for a fixed controller is
`max N 1 + A + 2`, where `A` bounds its statement actions before the input is
chosen. This is a proposed consequence of the unfinished height proof. Existing
time-derived space results do not establish it. The initialized empty-peek case
must retain live halt at five, outer none at six, coordinates
`[0,0,-1,0,0,0,0]`, and visits `{-1,0}`. A separate configured-start example has
different clocks and cannot replace it.

## Complete programme beyond this increment

Chapter 5 remains 92/94, with FDSA-5-92/93 open; Chapter 9 remains 61/110,
with FDSA-9-62 through FDSA-9-110 open. The
[inbox](../textbooks/inbox/README.md) retains interval-list, AVL and PFDS numeral
preparation, including source and lazy-work limitations. Canonical appendices,
source corrections and stronger historical drafts remain obligations.

VFA's qualified units retain their recorded source/evidence boundaries and
shared-library follow-ups. PFDS retains its complete book/thesis-union work,
including later exercises, evaluator-work correspondence, sharing/allocation
and exact-source availability limits. ADWH continues under its
[reconstruction map](adwh-reconstruction-map.md) and #149. The
[shared integration assessment](textbook-integration.md) and #558 connect these
books to existing library clients. No bounded machine task narrows this scope.

## Exact preservation and validation evidence

The [handover index](../history/textbooks/handover-2026-11-25/README.md) owns the
inventory and recovery check. Exact donor source reproduces tree
`394733a450268e8943048ea146440dcb75c7ceea` from public base
`ec4949a94ed70084d70f5b273fb0cc6dca8b2647`; that does not prove its mathematics.

| Needed information | Exact preserved owner |
|---|---|
| Full cumulative requirements and historical operating context | [requirements.md](../history/textbooks/handover-2026-11-25/received/current/control/requirements.md). |
| Detailed progress, immutable task requirements and historical gates | [donor CTB](../history/textbooks/handover-2026-11-25/received/current/source/docs/textbooks/CTB.json), [donor coverage](../history/textbooks/handover-2026-11-25/received/current/source/docs/textbooks/coverage.json). |
| Complete mathematical derivations and embedded literal case records | [original preparation](../history/textbooks/handover-2026-11-25/received/current/source/docs/research/fdsa-rotation-certificate-preparation.md). |
| Standalone useful drafts, expectations and reconstruction maps | [research index](../history/textbooks/handover-2026-11-25/received/current/research/README.md), [path map](../history/textbooks/handover-2026-11-25/received/current/research/RESEARCH_PATH_MAP.json). |
| Historical independent review and whole-run outcomes | [review handoff](../history/textbooks/handover-2026-11-25/received/current/evidence/reviews/HANDOFF155.md), [outcomes](../history/textbooks/handover-2026-11-25/received/current/evidence/history/OUTCOMES156.json). |

The preserved giant paper and catalogs remain exact recovery inputs. Current
papers summarize their contracts and link to the full sources; they do not
replace missing evidence with a success claim. Historical source-reading limits,
printer limits, failed attempts and UNKNOWN whole-run results keep their original
scope. The receiving acceptance record must name the actual validated candidate
and both review outcomes. Preservation alone supplies neither.
