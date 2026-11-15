# Existing import footprint prerequisite — version 1

Context: full project validation has made little progress under an 8GiB memory
limit with severe major-page-fault reclaim; compilers map the entire Mathlib
closure. Two existing FRP files import the all-library aggregate. A later
filesystem-full error also blocked Nix evaluation; offline use of the existing
pinned closure works, with cache archives cleared and completed worktrees removed.

Scope: replace only those broad imports with their mathematical/tactic
providers. Preserve every declaration, proof body, statement, example and audit
root byte-for-byte, unless a separately recorded missing direct import elsewhere
requires adding its provider. No toolchain, dependency pin, gate, guard, axiom
allowlist or source-policy relaxation. Formal checks still require all 957
integrated project modules and the exhaustive audit.

Fixed base 70a1477d822efd4fdcec2007280f650bb4695eda. Candidate worktree validation-imports,
branch pfds/import-footprint, private outputs; external packages read-only shared.
Source-only cross-cutting prerequisite ticket 10018; not Chapter2 acceptance.
Focused compilation is developmental evidence. Require isolated exact candidate
full check, success record, final verify, and both independent review axes. If
transitive-import consumers fail, add their real direct dependencies without
changing definitions/proofs. Keep source-change and resource claims separate;
measure actual closure/build outcomes before claiming improvement.
