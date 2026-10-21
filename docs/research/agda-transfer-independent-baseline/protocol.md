# Independent second-transfer protocol for #106

Status: Phase 1 selection recorded; independent scope review pending. No Lean
proof construction has begun. This protocol contains the declaration and scope,
not a proof solution. Give the scope reviewer this file, not the archived
upstream implementation. Candidate and protocol may be frozen after that review;
this document does not claim the review has passed.

## Authority and author provenance

Task: [#106, Evaluate Agda proof reuse with an independent fresh author](https://github.com/VladimirMarko/conaled/issues/106).
The fetched issue has `updatedAt = 2026-10-21T14:20:46Z`, with no comments.
Its complete requirements are preserved in `evidence/issue106.json`.

The author is the fresh Codex agent receiving the Phase 1 delegation from
source thread `01a15e19-8acb-7382-8a5c-b422d736d3d6`. The receiving session's
unique platform ID is not exposed in the supplied context. This author has
neither implemented nor reviewed #104/#105 in this session and received no
implementation conversation, private notes, theorem choice, or solution plan.
The platform launch configuration is not independently inspectable here;
fresh-author provenance rests on the supplied delegation and the actual inputs
listed below. The orchestrator should retain its launch evidence separately.

All filesystem work is confined to `/home/vlad/Code/conaled-independent-106`.
Verified HEAD: `8b1ed308f29cbe9d00e03c8b6b7780ffeb4b7c17`.
Initial `git status --porcelain=v1` was empty, including the index. That HEAD
is the fixed baseline. No history beyond HEAD or sibling checkout was read.
No commits, synthetic commits, pushes, tracker writes, reviewer agents, or
implementer requests have been made. The user explicitly limits `$implement`
to Phase 1, overriding its normal implementation/review and snapshot sequence.

Only `baseline106/` is authored here. The frozen API remains read-only.
Prepared build caches are not additional source/API inputs. No build cache
contents have been consulted, and no project or Lean build has been run.

## Selected upstream declaration

Select `foundation-core.identity-types.assoc` from UniMath/agda-unimath,
revision `75518656f287c203b41cb7f71df46e02b987a084`:

[Pinned identity-types source](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/identity-types.lagda.md).
The declaration appears under “Properties / Associativity of concatenation /
Associators.” Its enclosing parameters and exact declaration are:

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
```

License: MIT, copyright (c) 2022 Egbert Maarten Rijke. The complete notice is
retained in `evidence/LICENSE.md`, fetched from the
[same revision](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/LICENSE.md).
Retain that notice with any later adaptation. No Agda build or upstream
typechecking has been performed.

This theorem relates two parenthesizations of three arbitrary composable
paths. Its conclusion is an identity between paths, not transport composition
on a primitive fiber element. It is neither a renamed `tr-concat` nor a
restriction to reflexive inputs. The input paths remain arbitrary.

## Declaration dependency closure and scope

The declaration-level closure is:

| Item | Pinned origin and role | Intended frozen-fragment treatment |
| --- | --- | --- |
| `Level`, `UU` | `foundation.universe-levels`, which publicly imports `Agda.Primitive` and renames `Set` to `UU` | External signature parameter for the primitive base; no internal universe term |
| `A`, `x y z w` | Enclosing type parameter and four elements | Primitive base and generated context entries |
| `Id`, `_＝_` | `foundation-core.identity-types`; notation expands to `Id` | Generated identity formation, including identity over a path type |
| `_∙_` | Same module; composable path concatenation | Existing named source `concat`, retaining its upstream convention |
| Function/dependent argument notation | External universal quantification over the displayed inputs | Contextual source judgment and host-level parameterization, no internal Π |

There are no further named mathematical declaration dependencies. The source
module imports `foundation.universe-levels`, whose only import is
`Agda.Primitive`. The needed builtin vocabulary terminates at `Level` and
`Set`; no Agda compiler revision is asserted or required for this source
inspection. Other operations and theorems in the identity-types file are not
dependencies merely because they occur in the same file.

At the rule level, the dependency operations and upstream proof use identity
formation, reflexivity, identity elimination and its computation, plus ordinary
context/parameter machinery. The fragment documents these rules and finite
dependent tails. This is a rule inventory, not an elimination plan. Neither
transport nor inverse nor `trConcat` is a mathematical dependency of `assoc`.
There is no univalence, extensionality, K/UIP, equality reflection, modality,
crisp rule, HIT, truncation, or resizing requirement in this closure.

The scope claim is declaration-level suitability, not a claim that the frozen
author API already makes this proof convenient or even practically reachable
within the budget. In particular, existing named `Path` values describe base
paths; the selected conclusion is an identity between such paths. Whether
generic derivations and interpretation suffice without added API is an
experimental question. Missing conversions or consumer interfaces must be
recorded, not silently supplied by framework edits.

## Intended conclusion and applications

The source goal, in mathematical notation, is a generated term of

```text
Id (Id Base x w)
   (concat (concat p q) r)
   (concat p (concat q r))
```

under arbitrary well-typed `x y z w : Base`, `p : Id Base x y`,
`q : Id Base y z`, and `r : Id Base z w`. This is a contextual judgment,
not a request to add internal dependent functions or encode the displayed
notation as unchecked raw syntax. Statement review must check endpoints,
parentheses, identity level, quantification, and preservation of arbitrary
input paths. Native Lean equality or a semantic associativity theorem cannot
substitute for the source identity derivation.

The expected ordinary application in an arbitrary ordinary groupoid is
`(p ≫ q) ≫ r = p ≫ (q ≫ r)`, obtained by interpreting that same source
derivation and comparing interpreted concatenation with actual composition.
It must retain arrow labels. Planned checked specializations use the frozen
documented C₄ one-object model with its translation family and its trivial
family. They should compare the same composed arrow and the resulting action
on a fiber element under both parenthesizations, including nonidentity labels.
These prospective applications test reuse of one source proof; they do not
claim a new groupoid law, faithful trivial action, smooth descent, or general
higher-groupoid coherence. A general contextual caller and substitution use
should accompany the concrete checks if the frozen interface permits them.

The later direct-Lean comparison concerns the same arrow equality and
applications. It is deferred until the unassisted baseline is archived, so
it cannot become a substitute proof path during the experiment.

## Prospective budget and stopping rule

Phase 1 ends with this document and evidence. Stop now for a separate,
solution-free independent scope check. Do not begin Lean proof work, write a
proof skeleton, or launch reviewers in this phase. The reviewer should assess
the declaration, closure, intended applications, independence, and budget;
it must not return a proof, motive, helper implementation, or tactic advice.
Record its disposition and freeze an exact protocol digest before Phase 2.

For the later baseline, the proposed author budget is 40 substantive work
cycles total, shared across dependency/API investigation, translation,
proof-local helpers, debugging, and semantic applications. A cycle consists
of one recorded investigation or one logically grouped edit followed by its
targeted check. Multiple checks within a cycle are recorded separately.
After 10 cycles without a candidate source judgment, archive progress and
continue only within the same 40-cycle bound; do not reset the counter.

Stop earlier on success with validation, a demonstrated unsupported rule or
required frozen-API change, contamination by assistance, or an instruction
to stop. A concrete interface obstacle should include its attempted judgment
and exact diagnostic. If the limit is reached, archive the partial attempt and
report negative or inconclusive evidence. Do not weaken the theorem, switch
candidates, repair the framework, or request coaching to force success.

After construction succeeds within that budget, allow at most two full fresh
validation invocations (initial and one rerun). Any source corrections remain
within the same author budget. Infrastructure failures and machine wait time
are reported separately; unresolved build/audit failures prevent a success
claim. Before formal work, read and apply the local EDD skill, including its
statement review. Use the pinned shell and the repository's fresh build and
exhaustive axiom audit for any eventual success claim.

Maintain an append-only attempt log and preserve failed caller versions and
diagnostics outside the production import closure. Label each cycle as
dependency investigation, proof translation, helper writing, debugging,
application, or validation. Record exact commands, outcomes and interventions;
record actual timing/token data only where observable. Cycle counts are the
prospective control measure, not estimated person-hours. Do not infer effort
from line counts or elapsed build time. Framework construction in this
baseline is zero by constraint; proposed additions belong in a separate report.

Archive the baseline before feedback or assisted work. Subsequent help must
be labeled separately and cannot replace the independent outcome. Issue
publication and evaluator work belong to later authorized phases, not this one.

## Actual inputs and Phase 1 evidence

Inputs received: the delegation and its restrictions; repository instructions
supplied in the conversation; standard tool/system instructions and skill
catalog metadata. Skill catalog paths in the sibling checkout were not opened.
No other session context or private files were requested or read.

Frozen files read for instructions and documented scope:

- `AGENTS.md`, `README.md`;
- `.agents/skills/implement/SKILL.md`;
- `.agents/skills/no-ai-slop/SKILL.md` and its
  `references/ai-writing-detection.md`;
- `docs/agents/issue-tracker.md`, `domain.md`, `architectural-quality.md`,
  and `review-loop.md`;
- `GLOSSARY.md`, `docs/language-direction.md`, `docs/adr/README.md`,
  ADR 0001 and ADR 0010;
- `docs/research/agda-transfer-handoff.md`, `agda-transfer-interface.md`,
  and `agda-transfer-source-notice.md`.

Some combined command output was truncated; these reads are declared as
exposure, not a claim of complete inspection of every displayed file.
The handoff and source notice were visible in full. Local source inspection
was limited to search matches in `SquareKit/GroupoidTransport.lean`,
`SquareKit/Internal/PathTransport/Authoring.lean`, `Named.lean` and
`Typed.lean`, plus lines 190–272 of `Typed.lean`. No local Lean proof was
written or attempted. File discovery listed paths in the checkout and
`.agents`; this did not read other file contents.

Public inputs fetched: #106 via read-only `gh issue view`; the three pinned
upstream files archived below; and the pinned upstream root directory listing
via read-only `gh api` to locate the license. The complete identity-types file,
including its upstream proofs and neighboring declarations, was inspected.
That is permitted upstream-source exposure, not an implementer-supplied
solution. No Lean translation of the selected theorem was received.

One dependency-discovery command failed: fetching upstream `/LICENSE` returned
HTTP 404 and stopped that Python script before its issue-save step. The root
listing identified `/LICENSE.md`; a subsequent command fetched it and saved
the issue successfully. No proof/checker failures exist yet.

Archived byte-level evidence, SHA-256:

| File under `evidence/` | Digest |
| --- | --- |
| `identity-types.lagda.md` | `865065827674110a417d61adcbe8462fe77d5126d7f810804e3f723a8bbf908d` |
| `universe-levels.lagda.md` | `7dfb0cdda6264ae641b0eea90492bc942ca219768df04c3882de927fa6c26ac8` |
| `LICENSE.md` | `2313ef68bef65ddbc08c41ff7dbb64ad4cc77fcbb97fa0898698e5d16e2f5e59` |
| `issue106.json` | `53388435271bed51fd9fffd6232f1941dabde076cfa4b6c11308ab5d25f21c28` |

The upstream evidence contains proof bodies and is an author provenance
archive. Keep it out of the solution-free reviewer packet. No contamination
from private implementation context has been observed. Phase 1 is complete;
the independent scope review and all #106 proof/evaluation gates remain open.
