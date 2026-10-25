# Higher bridge issue reassessment

Inspected 2026-10-25 at `b0b19860f8b09b44c9b3b8f51f1b936975c3efad`,
against the previous integration checkpoint `afca87c`. This is a source and
tracker assessment, not a new originator review or fresh build. The findings
below record the initial inspection. The final section records the tracker
reconciliation authorized and completed afterward on the same date.

The first ordinary-groupoid source transfer now exists. Its remaining author
interface problem is supported by an unsuccessful independent experiment and
an incomplete repair. Smooth integration has better inputs, but its
restriction/descent obligations have not been implemented. General transverse
pullbacks still have no identified role in the selected application.

## What changed in the identity fragment

Commits [`2e7fe68`](https://github.com/VladimirMarko/conaled/commit/2e7fe68)
and [`8267b71`](https://github.com/VladimirMarko/conaled/commit/8267b71)
implement #104 and #105's typed contextual identity elimination and first
transfer. The [implemented interface](agda-transfer-interface.md) supersedes
the proposed operations described when #101 closed. In particular:

- [`Typed`](../../SquareKit/Internal/PathTransport/Typed.lean) has generated
  context, type, term, substitution and conversion judgments. Its contextual
  J admits finite dependent tails. Raw syntax, generated conversion and
  model-parametric annotation equality remain distinct.
- [`GroupoidModel.Instance.fullModel`](../../SquareKit/Internal/PathTransport/GroupoidSoundness.lean)
  constructs the groupoid interpretation, including `contextualJ_beta` and
  `contextualJ_sub`. Its primitive family is set-valued; independent external
  object, arrow and fiber universes are handled by `universeModel`.
- [`TransferConsumer.interpreted_trConcat`](../../SquareKit/Internal/PathTransport/TransferConsumer.lean)
  consumes the interpretation of the generated source proof.
  [`UniversalTransfer`](../../SquareKit/Internal/PathTransport/UniversalTransfer.lean)
  supplies the general ordinary consumer exported as
  [`SquareKit.GroupoidTransport.transport_concat`](../../SquareKit/GroupoidTransport.lean).
  The public wrapper does not require ordinary clients to construct syntax.
- [The retained callers](../../Examples/AgdaTransferCaller.lean) and
  [model cases](../../Examples/AgdaTransferModels.lean) exercise that same
  source proof, substitution and the label-sensitive faithful and ineffective
  C4 families. This is more than the initial `9199569` groundwork.

The independent #106 author did not finish general associativity within its
prospective budget. Its [archived report](agda-transfer-independent-baseline/report.md)
and [evaluation](agda-transfer-independent-baseline/evaluation.md) identify
dependent substitution and annotation alignment as the recurring difficulty.
This establishes authoring friction for that test, not impossibility of the
calculus or a measured cost for porting a whole library.

Commit [`be36b9b`](https://github.com/VladimirMarko/conaled/commit/be36b9b)
adds reusable congruence helpers but does not complete #107. The
[repair record](dependent-congruence-repair.md) identifies the missing comparison
between a substituted operation and a freshly constructed operation in a
different dependent-context presentation. General associativity, the final
handoff and a successful freeze remain absent. The existing frozen #105
[handoff](agda-transfer-handoff.md) is not a #107 freeze.

## New reusable evidence and its limits

| Development | Useful input | Limit relevant to #36/#103 |
| --- | --- | --- |
| #141, integrated in `55c4129` | [`GroupoidTransport.Route`](../../SquareKit/GroupoidTransportRoutes.lean) packages a base functor and natural fiber map; composition and reindexing preserve transport. [`Examples.GroupoidRoutes`](../../Examples/GroupoidRoutes.lean) compares the existing source term through two routes, retains ineffective labels and consumes the source-derived concatenation theorem in `two_transports`. | `Route.transport_concat` itself is a direct functoriality proof. It cannot replace #103's source interpretation. The fixture adds no general authoring operation or smooth restriction/descent theorem. |
| #142, integrated in `7634ec0` | [`DoubleDelooping`](../../SquareKit/DoubleDelooping.lean) and [second-identity examples](../../Examples/SecondIdentity.lean) retain nontrivial 2-cells and prove observation loss under truncation. | [`Internal.TwoLoop`](../../SquareKit/Internal/TwoLoop.lean) is a separate algebraic source at a fixed object and arrow. It has no dependent J and is not an extension of the PathTransport model to general higher identities. |
| #143, integrated in `ddc99ce` | [`FiniteUniverse`](../../SquareKit/FiniteUniverse.lean) constructs codes with bijections, equivariant decoding, finite dependent sums/products and family comparisons. | These are semantic finite constructions. They do not add universe rules to PathTransport, univalence, a general small-map classifier or a smooth universe. |
| #147, integrated in `neb37ef` | The [bounded elaboration experiment](bounded-elaboration.md) separates source fidelity, target admissibility, constraints, successful checking and environment extension. | Its natural/vector source is different from PathTransport. Its substitution laws do not settle #107's model-parametric dependent-context comparison. It did not run #108's independent experiment. |

These developments make model-change requirements and loss of information
more explicit. They provide examples and possible adapter contracts. They
do not justify replacing the selected source fragment, requiring one shared
AST, or treating the independent author gate as completed. The current
[language direction](../language-direction.md) still requires reducing
author obligations, with distinct semantic settings remaining expressible.

## Discrepancies found before reconciliation

| Issue | Assessment | Proposed tracker change |
| --- | --- | --- |
| [#102](https://github.com/VladimirMarko/conaled/issues/102) | Its original technical work is much further along: the first transfer and constructed ordinary-groupoid semantics exist. Economical independent reuse remains unestablished; the failed experiment exposed work the original proposal did not quantify. | Reconcile the original checklist and #104/#105/#106 child statuses with their recorded reviews. Retain #107/#108 and the existing repair/retest gate. Do not close #102 merely because `tr-concat` is proved. Its current body already records the approved repair route; that gate needs no reinvention. |
| [#103](https://github.com/VladimirMarko/conaled/issues/103) | Easier to specify technically because exact typed judgments, source proof and consumer are available. The smooth-model work remains; entry is also gated by the author-interface decision. | Replace future-tense descriptions of the missing first port with the concrete declarations above. Add #141 as reusable route evidence with its source/smooth limitations. Preserve the existing #107/#108 decision gate, source-proof requirement, all-parameter restriction/descent, boundary isomorphism and arrow orientation. Do not mark ready on the basis of semantic route fixtures. |
| [#100](https://github.com/VladimirMarko/conaled/issues/100) | The map understates implemented source work and omits the current repair/retest path from its main table. | Replace “higher operations remain proposed” in the #101 row and “Groundwork at `9199569`” in the #102 row. Distinguish completed first transfer, completed negative experiment, partial repair and pending independent retest. Update #103's gate to include #107/#108. Reconcile its first two completion boxes against the accepted technical evidence, without checking integrated smooth soundness. |
| [#36](https://github.com/VladimirMarko/conaled/issues/36) | Shared-language experiments now cover more models and preservation contracts. The full combined higher/differential/cohesive model remains missing. | Refresh the opening integration paragraph, which still calls #99 provisional and schedules #101/#98 as future independent work. Name accepted #98/#99, implemented first source transfer and the remaining smooth integration plus author gate. Keep the already-added #128–#131 workstreams distinct; no duplicate super-issue is needed. |
| [#97](https://github.com/VladimirMarko/conaled/issues/97) | No demonstrated change in mathematical difficulty or application need. | Retain deferred status and the named-application re-entry condition. An optional dated status note can say the new groupoid/compiler work supplies neither an ordinary transverse fiber product nor its all-stage comparison. No new implementation blocker should be invented. |
| Closed #95/#96/#98/#99/#101 | Their accepted scoped results remain useful. Historical descriptions of then-missing source interfaces have successors. | Preserve historical acceptance and closure. Where useful, add successor links to #104/#105 and the current #102/#103 gate rather than rewriting old review claims as if the later implementations existed then. |

#104, #105 and #106 were still open in the tracker during this inspection,
although the [#102 report](https://github.com/VladimirMarko/conaled/issues/102#issuecomment-6322541685)
records reviewed technical work and the independently evaluated experiment.
Their state needs reconciliation with those exact acceptance records, not
automatic closure based only on this source inspection. The unsuccessful
transfer in #106 is a permissible completed experiment, distinct from a
successful proof port. #107 and #108 are explicitly incomplete.

The old research issue #35 also needs its own acceptance audit against current
research and implementation evidence. Neither its relationship to #36 nor
the existence of later research notes settles every item in its specification.

## The unchanged smooth obligation

No files matching `*Smooth*` or `*Quotient*`, nor `lean-toolchain` or
`lake-manifest.json`, changed between `afca87c` and the inspected HEAD.
The selected source interpreter does not import the smooth quotient modules,
and the smooth transport module does not import PathTransport. These checks
support a bounded conclusion: the new source work has not already supplied
the selected integration through those interfaces. They are not a proof that
no differently named reusable lemma exists elsewhere.

The next model construction still has to identify the admitted quotient
contexts and tangent families, interpret the existing source judgments, and
prove their parameter restriction and descent compatibility. Instantiating
the ordinary groupoid theorem separately at each parameter would supply only
the objectwise part. The actual quotient arrow, fixed-fiber transport,
orientation and classical derivative comparisons remain the contracts in
[#99's record](finite-quotient-tangents.md).

For #97 the unchanged dependency pin preserves the basis of the existing
[transverse-pullback assessment](transverse-pullback-decision.md). The new
finite classifier and presheaf universal properties concern different
objects; they do not construct the ordinary manifold fiber product or its
comparison at infinitesimal stages. There is no current evidence to reverse
the deferral.

The practical sequence is to reconcile the tracker, finish or explicitly
redirect #107's bounded structural experiment, conduct #108 under its existing
independence protocol, then resolve #103's entry gate. Broader classifier,
elaboration, higher-cell and universe experiments can inform those choices
without silently expanding that sequence into a full HoTT/SDG rebuild.

## Reconciliation completed, 2026-10-25

The owner authorized resolving the discrepancies and retaining this note.

- Updated #36's opening integration status, #100's map and completion evidence,
  #102's original technical checklist and completed child statuses, and #103's
  concrete source/model inputs. The newer route examples are identified as
  reusable evidence with explicit limits.
- Closed #104, #105 and #106 after checking the retained originator/ordinary
  review records and exact committed-tree identity. The pairs were
  `2e7fe68` / `afc3390`, `8267b71` / `8b1ed30`, and
  `429c7cc` / `ad14b67`, respectively. #106 closes as a completed negative
  experiment; its general source proof remains unfinished.
- Audited #35 against its four research deliverables and closed it. The
  capability matrix and source-specific sections, reuse recommendations and
  Felix comparison, specified graph experiment, and staged plan supply those
  deliverables in `internal-languages-lean.md`. This is acceptance of the
  recorded survey, not a fresh upstream survey or verification of present
  maintenance status.
- Added a dated #97 reassessment confirming deferral. Kept #107 incomplete,
  #108 pending its reviewed freeze, and #103 gated on #102/#108. No new
  implementation work or automatic further repair cycle was authorized.
- Preserved the closed historical #95/#96/#98/#99/#101 acceptance records.
  Current successor information lives in the updated map and consuming issues.

The first two #100 completion boxes and original #102 technical boxes refer
only to the accepted bounded interface and first proof. They do not certify
independent authoring economics or smooth source soundness. No source or
mathematical statement changed; this reconciliation did not run a fresh Lean
build or replace the original validation records.

Published acceptance/state records:

- [#35 reconciliation](https://github.com/VladimirMarko/conaled/issues/35#issuecomment-6402037921).
- [#104 reconciliation](https://github.com/VladimirMarko/conaled/issues/104#issuecomment-6402036359).
- [#105 reconciliation](https://github.com/VladimirMarko/conaled/issues/105#issuecomment-6402036936).
- [#106 reconciliation](https://github.com/VladimirMarko/conaled/issues/106#issuecomment-6402037446).
- [#97 reconciliation](https://github.com/VladimirMarko/conaled/issues/97#issuecomment-6402039555).
- [#100 reconciliation](https://github.com/VladimirMarko/conaled/issues/100#issuecomment-6402039749).
