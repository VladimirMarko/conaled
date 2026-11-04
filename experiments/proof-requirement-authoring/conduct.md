# Conduct fixed before dispatch

Two independent authors receive the same E-then-W order and different fixed
routes. Author M uses manual abstraction. Author D additionally receives the
prepared dependency ledger. Each attempts both tasks once; no crossover.
Neither author designed these tasks or inspected private solutions. Record any
actual prior exposure before starting, including prior familiarity with #286.
No nested agents, external model calls, or communication between authors.

This is an assigned trial inside an existing implementation/review loop. Read
the supplied example-driven-development, architectural-quality and no-ai-slop
guidance before formal work or outcome prose. `guidance/` contains exact frozen
copies; its language-direction and worked-example files supply their local
context. Navigation references in those copies do not authorize access beyond
the allowlist. Use the frozen tasks for domain requirements and this conduct
file for environment, validation and review coordination. Do not start another
implementation workflow or attempt to fetch missing repository documents.

Use namespace `ProofRequirementTrial.Manual` for route M and
`ProofRequirementTrial.Assisted` for route D, including all helper declarations.
This permits later comparison in one checked environment without renaming the
submitted declarations. The coordinator preserves exact submitted bytes before
any import or packaging changes.

The coordinator launches both with `fork_turns=none`, inheriting its model and
reasoning configuration without overrides. Record metadata actually exposed by
the session; hidden serving revision, effective token usage and price remain
unavailable. This is one configuration, not a model comparison.

Each author gets 20 minutes from its recorded UTC start, including reading and
compiler work. Stop sooner when finished. The clock is not an effort or causal
productivity estimate. At the cap retain partial work; do not repair after the
cap inside the original attempt. Environment-only help is allowed and logged;
mathematical intervention ends the unassisted observation at its prior artifact
and must be reported as a separate assisted continuation. No silent fixes.

Use `direnv exec . python check_attempt.py attempts/AttemptNN.lean` from your
handoff root. This runs `lake env lean` on an immutable source snapshot and
records raw diagnostics, exact command, source hash, UTC times and exit status.
The source can import `Examples.ProofRequirementSupport`. Before each check,
save the complete source under a new filename. Preserve raw stdout/stderr,
exit status, UTC start/end and exact command for every invocation, including
setup failures. Never overwrite an attempted source or its diagnostics. Keep a
plain command transcript as well as raw tool records where available. No agent
session transcript export tool was exposed at freeze. Preserve shell evidence
and the authored transcript; do not reconstruct them as a raw agent session
transcript. If an export later becomes available, archive it separately.

Only write inside `attempts/`. Support and task inputs are frozen. No `sorry`,
`admit`, new axioms or native-evaluation axiom shortcuts in success artifacts.
Failed files remain labeled evidence, never accepted theorems. The coordinator
rechecks successful artifacts under the same frozen contract and runs the
repository's exhaustive axiom audit after author attempts close. Authors need
not access the repository entrypoint or private reference imports.

Review statements for quantifier order, sufficient and inhabited assumptions,
exact equality, retained subtype projections, and actual use of the generic
result in both interpretations. Do not alter expectations to obtain green.
