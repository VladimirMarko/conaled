# Local #1022: narrow the finite temporal foundation's imports

## Scope and baseline

This is cross-cutting support for the user's whole-book formalization, within
the existing Preface/Perm implementation and review loop. It advances no book
chapter. Tickets and review evidence stay local; recovery checkpoints are
exposed and uploaded immediately after creation.

Baseline: `bed44c16cee3e1eff6a4175bad9a7ed50651b927`. Before this work, root
verified both main and isolated candidate HEADs at that commit and both full
porcelain outputs were empty. The enclosing review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The existing `SquareKit/Temporal/Finite.lean` imports `Mathlib.Tactic` and has
SHA-256 `a5250768a66bb6103b3edb188f4ec370f2e9f9f8937ea066c914b3f6056b90a9`.
Its actual completed setup contains 3,121 artifact mappings. Its integrated
reverse import closure has 34 modules, counting the changed root. The ongoing
candidate build took 756 seconds for FRP.Temporal; an earlier bounded diagnostic
observed substantial paging with little user CPU. These observations motivate
a smaller dependency load, but do not establish a controlled speedup.
The read-only proposal and exact dependency evidence belong in
`../validation/temporal-import-proposal.md`.

## Exact proposed change and bounded staging check

Replace only `import Mathlib.Tactic` in Finite by these two explicit imports:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Convert
```

Preserve every non-import byte. The second import documents the proof's direct
tactic dependency even though Fin.Basic currently reaches it through
Tactic.Common; it does not increase the proposed dependency closure. Do not
change any definitions, theorem statements, proofs, comments, namespace/options,
tooling, dependency pins, audit, or public coverage. Monitor is outside this
initial scope.

Use one isolated full-module staging invocation, initially bounded to 180
seconds with a five-second termination grace and `LEAN_NUM_THREADS=1`. Keep
the original module name, package, options, module mode and compiler flags.
Copy the actual completed Finite setup and preserve every mapping and other
field; there must be no imports override. Both proposed modules must resolve
to the already completed pinned artifacts. Record the actual candidate
compiler command and LEAN_PATH rather than infer them from another module.
All compiler outputs must go only under the new staging directory.

Before and after, verify identities of the original main/candidate source,
actual setup, and the completed mapped artifacts of the two proposed direct
imports. Keep all dependency inputs stable; the final full gate still checks
the complete candidate under the repository integrity discipline.
Record complete command, timeout/exit status, diagnostics, source/setup hashes,
and emitted direct-import metadata. A successful focused check is evidence for
this import-only proposal, not validation of all 33 clients. A concrete missing
declaration may justify one explicitly recorded import-only adjustment; no
proof edits or repeated unbounded search are authorized by this initial test.
Do not change the active candidate, dependency/build caches, or any primary
process. Only one auxiliary compiler may run, and no broad auxiliary build or
cache fetch is allowed. Hash generated staging artifacts and remove them after
metadata extraction unless root explicitly requests a bounded client check.

## Integration and acceptance

Root decides whether to integrate from the actual result. A successful
prototype permits proposing this one-file import replacement. Before changing
the isolated candidate, preserve the current build's true outcome and stop only
its verified task-owned processes if that run is deliberately superseded. Keep
all prior results, including incomplete or interrupted attempts, truthful.

Any integrated change creates a new exact candidate and extends the enclosing
review to its entire diff from the unchanged base. The same independent
Standards and Spec reviewers must assess the source and completed validation
evidence. Normal `./check.sh --candidate HEAD` coverage, guarded compilation,
exhaustive proof audit, required proof-audit regression, and final
`./check.sh --verify-candidate HEAD` immediately before acceptance remain
mandatory. No tooling change or stale-artifact evidence currently mandates
fresh mode. Concrete downstream missing dependencies must be recorded and
resolved explicitly before acceptance; no client is assumed validated from
this focused check.

Preserve and immediately upload a recovery checkpoint after candidate
integration and again after acceptance. Preface must be accepted before Perm;
Sort implementation remains blocked until both are accepted.

## Concrete initial-check findings and bounded correction

The initial isolated full-module check returned exit 1 in 11.066 seconds, with
an unknown `Sigma.mk.inj_iff` at staged line 103 and consequent simplification/
funext diagnostics. It did not time out. All 23 protected inputs were unchanged.
The initial proposal incorrectly treated this lemma as already supplied by the
basic/core imports; retain that original proposal and failed evidence rather
than rewriting their history.

Pinned `Mathlib/Data/Sigma/Basic.lean:58` declares the exact lemma. One bounded
correction is authorized: add `import Mathlib.Data.Sigma.Basic` to the proposed
Finite header, preserving every non-import byte. Keep the initial attempt
frozen, use separate correction inputs/outputs/results, and apply the same
actual-setup/no-import-override, protected-input, 180-second single-compiler,
metadata-extraction and cleanup discipline. No further speculative retry is
allowed by this correction.

Root also established that the slow FRP.Temporal and TemporalCausality clients
inherit `Mathlib.Tactic` independently via Progress.Processors -> Streams ->
Evaluation. A Finite-only change cannot remove their umbrella dependency.
A read-only investigation of that second root is recorded separately in
validation/progress-import-proposal.md; no Evaluation edit or compiler has yet
been authorized. Integration must be decided with this impact caveat explicit.

## Evaluation path: explicit scope amendment and one bounded check

The corrected Finite attempt passed with exit 0 in 52.538727 seconds, no
messages or timeout, exact intended direct imports, and 45 protected identities
unchanged. Generated outputs were recorded then removed. This result validates
Finite's proposed header only; it does not remove the independently inherited
Evaluation umbrella from FRP clients.

Root has read the complete existing Evaluation source. Its SHA-256 is
`8882235188cd0e293f3433d220b677f160b539f4829f899ed2a911c655ca059f`. The read-only follow-up has identified core tactics and the three
`omega` uses, with the remaining mathematical support already supplied by its
unchanged `Applications.Optimization.Relations` import. Authorize one separate
bounded staging check replacing only `import Mathlib.Tactic` in
`Applications/Progress/Evaluation.lean` with
`import Lean.Elab.Tactic.Omega`. Preserve every other byte and the unchanged
Optimization.Relations import. No other umbrella root is in this scope.
The exact read-only evidence belongs in `validation/progress-import-proposal.md`.

Use Evaluation's own actual completed setup and compiler trace, not Finite's.
Preserve module/package/options/mode and every artifact mapping, with no imports
override. Core Lean imports use the pinned compiler distribution's ordinary
resolution; do not fabricate a package mapping for Omega. Protect the original
main/candidate source, actual setup, directly consumed completed
Optimization.Relations artifacts and the pinned Omega artifact identities.
Use separate staging source/setup/outputs/results under
`staging/progress-evaluation-import/`, the pinned Nix shell, actual original
compiler flags and LEAN_PATH, LEAN_NUM_THREADS=1, and the same 180-second bound
with five-second grace. The previous compiler must be finished before launch;
only one auxiliary compiler is allowed. On failure/timeout, freeze and report;
no retry is authorized by this Evaluation step. Record emitted direct imports
and remove generated outputs after hashing and metadata extraction.

Any integration now has at most these two changed source headers, with all
non-import bytes preserved. Their full affected client union, independent
Standards/Spec review, ordinary guarded complete candidate build and exhaustive
audit, required proof-audit regression, final verification and durability gates
remain mandatory. The current bed44c1 primary run remains untouched during
staging. Neither the static dependency counts nor distinct elapsed times prove
a controlled speedup.
