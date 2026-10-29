# Toolkit author trial protocol (#249)

Frozen before author dispatch on 2026-10-30, against source revision
`f071f18966d1ee875cdb5f328903d18a714732dd`. Do not modify these tasks during trials.

Both families use `Applications.Sequences.OrderedSummary` and ordinary Lean
lists/DLists. Public source and repository documentation are available, including
`docs/research/ordered-summary-implementation.md`, `Examples/OrderedSummary.lean`
and `docs/language-direction.md`. No private design discussion or proof hints.

## Contracts fixed before trials

A: established concrete client. For arbitrary `A`, arbitrary monoid `M` and
`measure : A → M`, construct the DList from `xs : List A` by left-folding
`Batteries.DList.push` from empty. Prove BOTH its full decoded sequence equals
`xs`, and its `summary measure` equals the left fold of right-multiplication
by `measure a` from `1`. Do not assume commutativity. Direct route proves these
from DList/List operations and summary nil/singleton/append laws using native
induction/fold lemmas, without `batch_*`, `dlist_batch*`, or shared reachable
fusion. Shared route uses the existing specialized/general batch interface.

B: new reverse-list realization and client. Represent sequence `xs` by a stored
list `r` with `decode r = r.reverse`; empty is `[]`, push is `a :: r`, and
concatenation is `append x y = y ++ x`. For arbitrary monoid and measure, retain
cache `(r,m)` with validity `m = summary measure (decode r)`; no invariant on
plain lists. Prove empty cache valid, append of valid caches valid, and BOTH
full batch decode and ordered batch summary after folding push from empty.
Direct route uses native List reasoning and summary primitive laws, without
shared validity/append/batch/fusion theorems. Shared route must discharge local
representation laws and derive these guarantees using `Valid`, `empty_valid`,
`append_valid`, `batch_decode`, `batch_summary` or existing public specializations.
Use the same operations and observations in both routes. Do not replace full
history by the summary, add assumptions, or reprove the shared library.

For each family include checked empty and nonempty applications. Include an
order-sensitive `FreeMonoid Bool` instance and a negative example explaining why
equal length does not entail equal full sequence; for B also a deliberately
invalid cache. Derive useful cases from the trial theorem where applicable.
No cost, bounded-storage, allocation, physical runtime or new-setting claims.

## Conduct and evidence

Two independent fresh authors, no history fork, inherited model and effort
without overrides. Exact serving model revision, token count and pricing are
not exposed; mark unknown rather than infer. This is one available configuration,
not a capability comparison. Each receives 15 minutes from its recorded start
or stops at completion. No nested agents or external model/API calls.

Author A order: A direct, A shared, B direct, B shared.
Author B order: B shared, B direct, A shared, A direct.
Reading public examples is allowed and must be recorded. Do not read the other
author's files. Later routes have prior exposure, so counterbalancing is not a
causal estimate. Do not adapt the interface or add public library helpers.

Work only in your assigned archive directory; sources elsewhere are read-only.
Use `direnv exec . lake env lean path/to/AttemptNN.lean` from the checkout.
Preserve EVERY attempted Lean source before running it, diagnostics, UTC start,
finish and exit status. Never overwrite an attempted file or its log. Record
shell/setup failures too. A final self-contained source may gather successful
routes in namespaces. Import `ProofAudit` and run `#audit_project_axioms` on the
final successful file to audit current-module claims as well as loaded modules.
Record the exact commands, toolchain, imports, assistance (including none),
concepts/obligations, wrappers/conversions, errors/repairs and statement review.
No admissions, new axioms or native-evaluation axiom shortcuts in success files.
Failed archived attempts remain evidence, explicitly not accepted theorems.

Authors report to the coordinator; no communication between trial authors.
Only environment clarification is allowed without marking a trial assisted;
any mathematical help must be recorded with before/after artifacts. Report
incomplete tasks honestly at the cap. Current author failure alone does not
establish a mathematical or Lean limitation. These are isolated experimental
artifacts, not integrated library modules. Do not change the contract for green.
