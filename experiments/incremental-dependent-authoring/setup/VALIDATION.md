# Setup validation before author dispatch

The prepared handoffs are `/tmp/conaled-351-357/author-baseline` and
`/tmp/conaled-351-357/author-candidate`. No measured author was dispatched by the
setup helper. The helper did not construct a solution to the mathematical task.

The baseline export has 40 local library modules; the candidate has 53. Adding
the same independent Spec gives 41 and 54 allowed modules. Their provisional
manifests list 53 and 66 public files. Both use the unchanged attempt wrapper,
the same pinned configuration, and private copies of the pinned dependencies.
Preparation records contain source and initial artifact hashes. The later
artifact-reduction record removes project trace and IR files that are unnecessary
for direct Lean checks and can mention donor checkout paths. Final imports use
only the matching compiled project closure and each arm's private dependencies.

The independently specified common module compiled in each handoff with no
diagnostics. Both final wrapper smokes imported their full entrypoint list plus
that Spec. `SetupTrue` passed with exit 0; `SetupFalse` failed with exit 1 for its
intentionally invalid proof. Each archive records verified public inputs before
and after checking, exact attempted bytes, dependency paths, commands, diagnostics
and hashes. The final checks took 2.09/2.00 seconds in baseline and 2.13/2.15 seconds
in candidate. These are setup timings, not author effort or proof performance.
Both handoffs have empty `attempts/` directories after archiving setup evidence.

Successful closure preparation took 11.18 seconds for baseline and 70.31 seconds
for candidate, as recorded by the script. These times omit earlier setup work
and corrections. The helper's total elapsed effort was not separately metered;
it must not be reported as zero or inferred from the successful commands alone.
The Spec focus checks were not timed. All scripts passed Python syntax checks.

The setup failures were:

- The trial directory initially needed the normal `direnv allow` step.
- The first baseline copy rejected all dependency symlinks. Batteries contains
  an internal `docs/README.md` link to its own README. The corrected check permits
  only links resolving within the private dependency copy. That first incomplete
  destination was removed and recreated before any author exposure.
- The first successful True smoke could not move its read-only archive directory.
  Its complete evidence was preserved under `smoke-baseline-initial`. The smoke
  helper now makes the archive directory writable for moving and restores its
  read-only mode outside the handoff. Both success/failure pairs were rerun.

These are coordinator/setup events. No failure above is counted as an author
attempt. The two later smoke pairs before and after artifact reduction are also
setup evidence. The final pair is under `smoke-baseline-final` and
`smoke-candidate-final`; earlier evidence is retained for provenance.

A fresh Git index lists only public files to keep Nix from copying dependency
caches. It has no commits, remotes, original history or object alternates.
The handoff boundary is an instruction and inventory contract, not an operating
system sandbox. Third-party dependency source remains available to both authors.
Final protocol review and coordinator freeze are still required before dispatch.

Evidence `.log` files are intentional experiment artifacts and must be included
with `git add -f` despite the repository's ordinary log-file ignore rule.
