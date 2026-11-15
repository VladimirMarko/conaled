# Chapter 1 repair: independent Standards source preflight

Recorded 2026-11-02 by the retained independent Standards reviewer
`/root/chapter01_review/standards`, within the existing Chapter 1 review loop.

## Outcome

**No new concrete Standards finding in this bounded source preflight. Final
Standards outcome remains Blocked on required validation and final review.**

Concrete Standards findings: **0**. Worst identified Standards issue: **none**.
This is not final approval, a third Spec review, or a replacement for checking
the elaborated declarations. SPEC-001, SPEC-002, SPEC-003 and SPEC-V001 remain
open. This assessment does not close, rerank or reassign those findings.

## Exact identity and scope

- Original base and confirmed merge base:
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Repaired candidate:
  `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Previous candidate:
  `1aabd512284fe86254278ac631eda061d311050b`.
- Isolated source checkout:
  `/workspace/scratch/845aa1048b05/conaled-ch01-cost-models`;
  HEAD matched the repaired candidate and its working tree was clean when read.
- Full review scope: `git diff BASE...CANDIDATE`, all 14 changed paths, with
  both commits `1aabd51 feat(resources): formalize FDSA basics (#174)` and
  `a14977b feat(resources): compare FDSA call observations (#174)`.
- Frozen original requirements: `chapter01-requirements.md`, SHA-256
  `7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba`.
- Frozen repair addendum: `chapter01-cost-model-requirements.md`, SHA-256
  `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.
- Governing user request: `fdsa-control/REQUEST.md`. The supplied frozen
  requirement identities are retained above; their contents were read.

No task source is excluded. The unrelated original historical checkpoint ZIP
is absent from this isolated candidate and remains outside the task scope.

The earlier Standards source analysis in `chapter01-standards-round1.md` is
retained where unchanged. The previous-to-repaired diff confirmed no change to
the six earlier Lean files (`EuclidInduction`, `CallCount`, `ListReversal`,
`Measured`, `Examples.FunctionalBasics`, `Examples.ListReversal`) or
`docs/SOURCES.md`. Their earlier architecture, universe-generalization,
statement and example assessments therefore carry forward. This does not
carry validation credit from the old candidate to the new candidate.

The new inspection covered all four new Lean modules, their actual supporting
`Measured`, `Workload`, `Potential` and `Growth` interfaces, the public-root
additions, the new call-model document, and the reconstruction-map changes.
The author statement review and handoff were read as evidence rather than as
independent approval. The retained Spec preflight remains a separate axis.

## Standards applied

The candidate's `AGENTS.md`, architectural-quality guidance, domain/glossary
and ADR index, code-review skill/heuristics, and example-driven-development
statement-review guidance were consulted. The unchanged README build policy,
ADRs 0001/0010 and shared language-direction analysis from the retained review
remain applicable. The user overrides GitHub ticket/publication conventions
with local tracking and durability checkpoints, not the formal quality gates.

## Architecture and methodology assessment

### Reuse and separation

`CallComparison` uses ordinary occurrence lists, finite suprema and Mathlib's
standard real-valued asymptotic interface. It extends the existing call-count
namespace without introducing another execution language. `SharedDemand`
returns existing `Resources.Measured` values; its cache-only `step` feeds the
existing `Resources.run`. Preservation uses `run_invariant`, and global cost
accounting uses `run_potential_exact`. These are actual proof dependencies,
not documentation-only reuse claims.

The function cache, cache validity, demanded-value agreement, remaining-work
potential and final inequalities have separate definitions or theorems.
Accounting does not assume value validity merely to count missed entries;
value correctness explicitly requires validity and establishes it from the
empty cache. No new preservation family or cross-setting transport claim is
introduced. The earlier `erasureSquare` universe change is unchanged and
retains its prior client-based justification, pending full compatibility
validation.

### Assumptions and nonvacuity

In `CallComparison.lean` lines 38-90, the refined upper bound is derived from
per-occurrence local bounds; no final total-cost comparison is a premise. The
family theorem fixes K before its eventual input quantifier. The finite
catalogue theorem supplies a supremum from structural membership, while the
trace remains a list and preserves repeated occurrences. Neither this
catalogue nor the coarse/fine comparison requires finite payloads. Empty
traces and zero tariffs remain in the domain.

The entry comparison at lines 92-119 explicitly retains pointwise or eventual
positivity for the forward multiplicative bound. Its unconditional reverse
direction and the real casts are explicit. It connects to the existing tick
operation rather than inventing an unrelated cost function.

In `SharedDemand.lean`, the cache is `ι → Option α`. Payload equality,
ordering and inhabitance are absent. `DecidableEq ι` is attached to operations
and laws using identity updates. `Fintype ι` begins only at the remaining-work
section, rather than restricting all requests or value laws. Fixed pure
callbacks make identity stability explicit. Empty-cache validity is proved,
and the arbitrary-prefix value theorem derives its result through validity
preservation and stored-value evidence. Its premise does not already assume
the returned-value conclusion.

The local conservation law is derived from the hit/miss transition and finite
sum decomposition; `run_work_remaining` telescopes it through the existing
executor. Natural nonnegativity then yields the eager-catalogue bound. This
does not postulate a whole-run inequality or require valid payloads for the
accounting identity. The empty catalogue with empty payload and the concrete
inhabited catalogue provide meaningful boundary and satisfiability cases.

### Connected examples

The examples connect independently stated expectations to public operations
and laws:

- `appendEvents_cost` relates the branch trace to actual `appendRun` cost;
  `append_refined_bounds` uses `catalogue_refined_bounds`, and the asymptotic
  client uses `refinedCost_isBigO`. Empty payloads and duplicate list values
  retain the intended counts rather than changing occurrence semantics.
- The measured-program entry client uses `tick_cost` and `add_entry_isBigO`;
  value preservation uses `tick_value`. The zero case and intermittent family
  expose the consequence of omitting positivity.
- Repetition uses `run_replicate_empty`; the finite catalogue bound uses
  `run_cost_le_eager`; skipped work uses `run_work_remaining`; demanded values
  use `request_after_run_value` with `empty_valid`. Arbitrary intervening
  requests use `run_preserves_cached` and `request_hit`.
- Arbitrary payloads with natural identities exercise the operation without
  finiteness. Equal payloads at distinct Boolean identities still incur both
  first-request charges. The empty catalogue also permits the empty payload
  type, avoiding accidental global inhabitance requirements.
- The duplication example uses actual cache requests and measured binds.
  `sharedLayer_eager` relates sharing to one eager bind; `unsharedLayer`
  performs two measured binds. The recursive families derive equal values
  and their distinct recurrences, rather than assigning strategy names to
  unrelated numeric sequences.

The author record preserves the independent arithmetic expectations and
identifies unresolved elaboration obligations. Some simple boundary claims
use reduction, appropriately supplementing rather than replacing the public
theorem connections above. No arbitrary per-helper example quota is applied.

### Scope, documentation and integration

The explanatory documents identify root/local-work coverage and exclude
unbounded uncharged primitive work from the finite-tariff argument. The
shared-demand bound is explicitly a callback-work observation: cache
administration is excluded, and applying the eager sum to an external program
requires a separate correspondence. The one-entry lemma is not advertised as
a transitive inlining transformation. No blanket language simulation,
compiler-stack proof or hardware running-time claim is made.

The reconstruction map explicitly corrects the earlier explanatory-scope
classification while marking the repairs unvalidated. The public root imports
both new example modules, which import the corresponding domain modules.
Placement follows the existing domain/example layout rather than duplicating
the book's chapter structure in the software architecture.

## Pending gates and limits

No compiler, Lake integrity hash helper, source-policy/audit process, Git
mutation, cache/configuration change, gate interruption or restart was
performed. Read-only source analysis cannot establish successful elaboration,
inferred signatures, proof-term checking, downstream universe compatibility
or exhaustive axiom compliance.

The repaired immutable candidate still requires matching focused builds,
applicable whole-candidate source-policy/public-coverage checks, complete
build, output-integrity checks, exhaustive audit, candidate identity evidence,
both independent final review outcomes, and immediate final
`--verify-candidate` before acceptance. Any elaboration repair changes the
candidate and requires matching evidence. The running gate on old `1aabd51`
cannot validate these additions or close SPEC-001/002/003 or SPEC-V001.

This new outside-source report is the only permitted write for this preflight,
released specifically by the coordinator during the checkpoint hold. All
other source, reports and control files remain unchanged by this reviewer.
