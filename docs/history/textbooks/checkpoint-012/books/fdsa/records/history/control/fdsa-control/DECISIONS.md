# Cross-cutting formalization decisions

These decisions implement the governing request and conaled's existing standards.
They do not reduce the eventual whole-book scope or waive chapter acceptance.
Recorded 2026-11-02; revisit a decision if a concrete source obligation exposes a
problem, retaining prior clients and recording the reason.

## Book coverage and code organization

Keep chapter order in tickets and the reconstruction map. Place Lean code by
reusable domain concepts in the existing module layout. Reuse standard and
project definitions when their actual semantics match; source-oriented adapters
must have checked correspondence. A familiar algorithm name or equality of final
outputs alone does not establish a matching implementation or cost recurrence.

## Partial source operations and empty Lean types

Isabelle/HOL's logical types and underspecified operations do not justify a
global `Inhabited` assumption on every Lean payload. For source operations such
as head, indexed selection and minimum outside their valid domain, prefer the
existing conaled failure interface (`Option`, where already used), or an explicit
validity proof/domain. Prove the book correspondence on the stated valid inputs.
If a concrete realization genuinely needs a default value or extra capability,
keep that requirement local and visible. Do not silently strengthen all targets
or change existing empty-input behavior.

Preserve existing indexing conventions. For example, conaled's selection API is
one-based and returns `Option`; the book uses zero-based valid ranks. A checked
index/failure bridge should relate them instead of changing existing callers.

## Resource observations

Name and retain each model: function calls, comparisons, copied cells, allocations,
retained storage and other observations are distinct. An explicit adapter may
relate two counts, as Chapter 1 adds the empty-call charge to copied-cell append.
No cost equality follows merely from semantic equality. Costs of source-specific
helpers and predicates follow the pinned recurrence, even where a chapter or
exercise changes the general primitive convention.

Instrument the actual recursive branches or prove a recurrence correspondence.
Do not assign the cost of a slow source algorithm to a standard optimized
implementation just because their values agree. State compiler/runtime/target
assumptions for any claim beyond the abstract model; do not add such claims when
the source itself offers only a conditional discussion.

## Source defects and exercises

Keep an explicit disposition for each source defect: exact location, printed
claim, correction supported by the mathematical context and formal companion,
and the checked corrected statement. For a meaningful false statement, retain a
small checked counterexample where feasible. Syntactic or typographical defects
can be documented through exact source comparison. Never prove a false printed
claim by changing definitions unnoticed or by adding an axiom.

Exercise solutions are part of the requested scope. A book instruction to solve
an exercise 'on paper' describes its pedagogical presentation; it does not waive
the user's Lean formalization objective. Exact mathematical conclusions and
inequalities should have Lean witnesses. Practical judgments and discussion with
no precise mathematical claim remain explicitly classified as analysis. An
open-ended exercise may have a documented concrete solution scope, provided that
it answers the exercise rather than omitting its hard requirements.

A mathematical assertion is not automatically analysis-only because its proof
is cited elsewhere or omitted from the book. Retain the asserted result as an
explicit obligation with the conditions and model needed for a faithful
statement; the cited paper itself does not become a whole-paper coverage goal.
For example, Chapter2's average-input and randomized-pivot quicksort claims
need precise distributions and duplicate/cost qualifications in addition to
the separate deterministic exercise. References with no mathematical claim
and practical judgments can remain analysis. Correct earlier inventory
classifications explicitly rather than allowing them to shrink scope.

Preserve the source's epistemic status as well as its formulas. An explicitly
open conjecture is a formal statement to identify and relate to the source,
not a theorem this task may assume or promise to prove. A conditional claim
retains its hypotheses; a false printed claim requires the correction process
above. Bibliographic references alone do not create additional coverage goals.

## Acceptance and recovery

An implemented declaration, focused build, source review, full proof audit and
accepted chapter are different milestones. The local tracker must say which has
actually occurred. Both independent review axes need the same immutable candidate
and matching applicable validation before chapter closure.

Recovery checkpoints may capture unfinished work. Each includes complete source
history, working edits, local tickets, exact saved requirements, provenance,
reviews and truthful validation status. Preserve named Git refs, staged and
unstaged changes, and binary/untracked files. Checkpoint saving never upgrades an
unfinished theorem or blocked review to acceptance.
