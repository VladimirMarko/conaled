# Comparative architecture and scaling study

## Decision and constraints

Before implementing #358–#361, reassess which architectural formulations best
serve a language whose mathematical setting is a first-class parameter. The
owner is concerned that recent experiments disproportionately tested suggestions
from the owner and constructions already convenient in this repository. The
study must be capable of recommending a replacement or a different research
agenda. Existing implementation is evidence about those examples, not a neutral
sample of possible architectures.

Repository baseline: `5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`.
This brief and the independent reports are new work, not part of that baseline.
Record exact versions or access dates for primary external sources. Read
`docs/agents/architectural-quality.md`, `docs/language-direction.md`, domain
instructions, glossary and relevant ADRs. The target is mathematical/general
architecture and agent usability at scale; human-productivity superiority is not
an MVP requirement. Separate mathematical results, encoding costs and measured
agent behavior. No current interface or host encoding is the required answer.

Preserve the ability to express independently specified meanings, selected
proofs/results and dependent/higher identity data. Distinct mathematical settings
may supply distinct equalities and admissible operations. Interpretations need
not be functions into one set-level carrier. Compiler clients may observe
representations under separate contracts. Construction, observation and change
of interpretation must retain their stated guarantees. Lean remains the current
trusted implementation host; assess alternatives without assuming wholesale
migration is necessary or forbidden. No migration is authorized by this study.

## Independent requirements and discriminators

Formulate requirements before assigning roles to current modules:

- Reuse a dependent argument in genuinely different settings; distinguish local
  assumptions from laws derived for arbitrary constructions.
- Retain a selected witness and its dependent action through two changes of
  context; reject replacing it by mere inhabitation or an indistinguishable
  endpoint pair.
- Compose independently admitted extensions and expose interactions or a failed
  joint interpretation rather than infer compatibility from separate validity.
- Preserve a declared observation while hiding representation details. Test a
  relational or higher-order observation that cannot be reduced to the existing
  arithmetic selected-packet case.
- Assess scaling in construction size, number of operations, number of settings,
  interaction between extensions and maintenance after changes. Universal
  composition theorems and finite author timing measurements answer different
  questions. Count setup and marginal obligations separately; do not extrapolate
  asymptotic effort from the small #357 sample.

These are a starting contract, not an exhaustive benchmark suite. Each assessment
must suggest a discriminating problem and its independent expected outcome,
including a possible failure of the incumbent. Do not solve only the convenient
fragment and silently drop the requirement that distinguished the alternatives.

## Candidate space and evidence

The existing approach combines local rule certificates, native dependent
judgments, commuting/relational squares, institutional capabilities, indexed
adjunctions and optional resource modes. Its rationale is local law reuse with
explicit selected evidence. Existing examples and #357 establish scoped
correctness/usability; their sampling and prepared helpers limit general claims.

Seed alternatives include comprehension/local-universes coherence, nominal or
other principled binding representations, bialgebraic/distributive-law accounts,
and semantic stress cases such as higher-order probability and open-system
relational hiding. Discover other approaches when primary evidence supports
them. The seed list is not a shortlist of winners. Distinguish alternative core
representations, derived coherence machinery and complementary model capabilities.
Do not reject a candidate solely for lacking a current adapter or easy Lean port.

Local evidence pointers (inspect claims, not just summaries):

- `docs/research/indexed-compilation-experiment-results.md`
- `docs/research/incremental-dependent-author-trial.md`
- `docs/research/semantic-traditions-coverage.md`
- `docs/research/dependent-architecture-reassessment.md`
- `docs/research/bialgebraic-dependent-reassessment.md`
- `docs/research/dependent-calculus-frameworks.md`
- `docs/research/external-language-foundations.md`
- `docs/research/external-computational-semantics.md`
- `docs/research/felix-parity-implementation.md` and pinned `docs/SOURCES.md`

Existing reports are discovery pointers, not substitutes for primary sources.
Cite code at the pinned repository commit, and source theorem hypotheses for
external claims. Distinguish source inspection, supplied receipts, local
execution, paper derivations and proposed tests. Do not run expensive full builds
or start new formalization: this phase is research, with no code mutation.

## Incoming independent orbifold evidence

The owner reports that a separate Agda formalization of Myers' *Orbifolds as
microlinear types in synthetic differential cohesive homotopy type theory*
(arXiv:2205.15887) is complete in the paper's setting and now investigates links
to classical orbifold theory. It compared several libraries, including conaled;
a report is incoming. That current artifact/report is not yet supplied here.
Do not infer its library rankings, theorem coverage, assumptions or conclusion.
Do not contact its session or invent a correspondence it has not established.

Historical inputs are distinct. Read the guides before using archived material:
`docs/history/orbifold/agda-checkpoints/README.md` describes earlier incomplete
Myers checkpoint22 and Kock checkpoints; the separate
`docs/history/orbifold/standalone-formalization/README.md` describes an early Lean
archive. Neither establishes the status of the latest Agda work. The user's
current completion statement is reported evidence, not a local audit of new
sources. Consult `docs/research/orbifold-motion-reassessment.md` for prior scope.

Use the orbifold problem as an independent requirements probe: synthetic
internal reasoning, retained isotropy/higher data, model validity, comparison
with classical presentations and executable realizations are distinct tasks.
A supplied hypothesis may be appropriate in the paper's setting; identify the
additional obligations for a concrete model/comparison instead of dismissing
conditional mathematics or claiming it already constructs such a model.

When the report arrives, pin its revision, library revisions and selected
statements; compare assumptions and observations on a shared problem. Classify
reported gaps as semantic, foundational, API, maturity, documentation or artifact
compatibility. Final architectural recommendations and release of #358–#361
remain pending that evidence or an explicit owner change of scope. Independent
research and an honestly scoped interim publication proceed now.

## Independent perspectives and outputs

Three fresh agents receive this same brief with no conversation fork. They must
not read each other's drafts or coordinate conclusions until initial reports
are saved. Prior involvement and missing evidence must be disclosed; fresh
context does not establish model diversity.

1. **Foundations and coherence**, `foundations-initial.md`: which assumptions and
   derived laws support the requirements? Compare dependent presentation/model
   boundaries and possible coherence alternatives; include synthetic/classical
   geometry obligations without inventing the incoming report.
2. **Implementation, use and scaling**, `scaling-initial.md`: inspect real native
   and shared clients, identify local versus recurring costs, propose matched
   scaling and maintenance tests. Compare formulations, not just code sizes;
   include migration and proof-checking costs without prejudging the winner.
3. **Alternatives and semantic coverage**, `alternatives-initial.md`: start from
   primary-source alternatives and formulate their own problems/advantages.
   Evaluate coverage omitted by recent selected examples; distinguish blockers
   from incumbent inconvenience and identify a test that could favor replacement.

Each report gives a recommendation, strongest evidence for retaining the current
approach, established findings versus risks/open questions, smallest useful
alternative/correction, discriminating tests, exact evidence and limits. Report
at least one consequential uncertainty rather than invent agreement or objections.
Agents write only their own report; no implementation, tracker mutations,
external-session messages or additional delegation. Root reads all initial
reports before synthesis, preserves them and records subsequent cross-exposure.

Publication follows the repository implementation workflow with independent
Standards/Spec review. Design assessments are not that acceptance review. An
interim publication is not completion of the evidence-gated architectural study.
