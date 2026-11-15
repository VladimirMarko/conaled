# Local #1021: narrow existing FRP imports

## Scope and authorization

This is cross-cutting support for the user's whole-book formalization request.
The user permits cross-cutting concerns and reversible local implementation;
all tracking and publication remain local, with immediate recovery checkpoints.
It is not a new book chapter or a waiver of any chapter gate.

The source baseline before this change is
`cba657b43ed57e15962858713b819058e7d3c3ca`. The enclosing Preface/Perm review
base remains `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Main and isolated
candidate source were clean at the start; no unrelated edits are included.

The existing `Applications/FRP/Spec.lean` and
`Applications/FRP/Equivalence.lean` are the only integrated modules importing
the entire `Mathlib` umbrella. The required initial project validation reached
the former after rebuilding ordinary missing dependency artifacts. At
05:34 UTC, its compiler had accumulated 419,266 major faults, with only 2.54
seconds of user CPU. This observation motivates checking explicit imports; it
does not establish a controlled performance comparison or a compiler defect.

## Intended change

Replace only the two `import Mathlib` lines with conservative explicit imports
that provide the existing definitions, instances, theorem references and
tactics. Preserve every other source byte, including all formal statements,
proofs, examples, comments, namespaces and options. Do not change tooling,
dependency pins, the audit, public entrypoints, or validation policy.

The exact proposed lists and the initial read-only source analysis are in
`../validation/frp-import-contingency.md`. Staging source, complete diffs,
identities, compiler commands, results and emitted import metadata are in
`../staging/frp-imports/`.

## Development evidence

Use the pinned Nix shell and compiler with the original module names/options,
`-o/-i/-c/--setup/--json`, and `LEAN_NUM_THREADS=1`. Staging outputs must remain
outside both repository checkouts. A setup's artifact-resolution map is not
an import override: verify that it has no explicit import list and that emitted
metadata identifies the narrowed source roots. A constructed setup must be
identified as such and preserve package/options/module mode.

Check the two changed copies, then the direct clients `Frontier`, `Finite`,
and `Examples.FRP`, one compiler at a time with a 180-second bound per initial
invocation. Map checked staging dependencies explicitly. A concrete missing
declaration may justify one recorded import-only correction; do not silently
modify client proofs or definitions. Focused checks do not establish validity
of the full downstream import closure.

## Integration and acceptance

1. Record the exact focused results and unchanged source tails. Decide whether
   to integrate based on those concrete results, not an asserted speedup.
2. Commit a two-file import-only change using local ticket #1021. Preserve the
   original validation attempt and its actual exit status if it is superseded.
   Never edit an actively validating checkout. Stop only verified processes
   belonging to this task before switching its candidate.
3. Capture and immediately expose/upload a recovery checkpoint containing the
   new candidate, local ticket, all source/evidence, and precise pending gates.
4. Validate the new clean isolated candidate with
   `./check.sh --candidate HEAD`, retaining the normal output-integrity guard,
   all integrated module coverage, and exhaustive proof audit. Reuse only
   ordinary guarded completed build artifacts. No tooling/pin change or stale
   artifact evidence currently requires fresh mode.
5. Run the required proof-audit regression in the same pinned candidate
   environment. Continue the existing independent Standards and Spec review
   loop on the entire nine-file task diff, retaining previous findings.
6. After both axes pass, run `./check.sh --verify-candidate HEAD` immediately
   before acceptance. Record the local #1021 result together with the exact
   chapter candidate; only then can Preface/Perm acceptance and Sort work
   proceed. Create and upload the acceptance checkpoint immediately.

There are 40 transitive integrated clients of the two changed roots in the
current lexical import graph, including `SquareApplications` and `ProofAudit`.
The full candidate gate, rather than the three focused client checks alone,
must cover their elaboration and proof dependencies.

## Concrete full-build correction, 2026-11-02

Candidate 777bab9's normal full build exposed a downstream dependency in
`Applications/FRP/Demand.lean:139:16`, theorem `pending_registered`.
After `simp_all [next]`, its existing `le_rfl` proof is expected to prove
`n < n + 1`. The old umbrella supplied a successor-order simplification
that is not in Demand's new narrow import closure. The pinned
`Mathlib.Order.SuccPred.Nat` supplies `Nat.instSuccAddOrder`, and its imported
`Mathlib.Algebra.Order.SuccPred` declares `[simp] Order.lt_add_one_iff`.

The proposed bounded correction expands scope to an explicit direct import
of `Mathlib.Order.SuccPred.Nat` in Demand. Every definition, theorem statement
and proof in that client must remain unchanged. Check one staging copy against
the actual completed candidate dependencies with a 180-second bound, preserving
its exact original setup settings and every current artifact mapping while
adding resolution entries for the new dependency. This is an explicit
full-build-driven scope amendment, not a claim that the initial two-file
prototype validated all clients. No speculative source correction is allowed.
If the check passes, commit a new candidate with a ten-file enclosing diff,
retain the actual old build error and interruption/completion outcome, and
repeat the same complete normal candidate gates and both independent reviews.
The active candidate checkout must remain unchanged until its process stops.
