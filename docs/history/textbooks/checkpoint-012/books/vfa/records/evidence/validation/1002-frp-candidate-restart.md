# Superseding the broad-import candidate with local #1021

2026-11-02. This is an explicitly unaccepted candidate transition, not a
validation success or an acceptance-policy change.

Old candidate: `cba657b43ed57e15962858713b819058e7d3c3ca`.
New candidate: `777bab9b2510deab54603c3df267e5c134a3e1e0`.
Enclosing review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

## Concrete change and focused evidence

Local #1021 replaces only the `import Mathlib` line in each of FRP Spec and
Equivalence with conservative explicit imports. All non-import bytes are
identical. The integrated files exactly match the staged, checked versions;
`1021-integration.json` records their hashes and full task scope. The original
seven-file comparison/permutation work is unchanged. The new full diff is nine
files, 469 insertions and two deletions.

`../staging/frp-imports/SUMMARY.md` and `FREEZE.json` preserve all focused
identities, setup mappings, commands, outcomes and extracted output metadata.
Spec, Equivalence and Finite passed. Frontier and Examples.FRP timed out after
180 seconds with empty diagnostic logs; neither is a pass. No corrections or
retries occurred. The two defining-module passes support putting this precise
change through the normal full candidate gate. They do not establish all-client
elaboration or a controlled memory/speed improvement. Generated staging files
were removed after their hashes were recorded, and none entered a project cache.

## Preserved old outcome

The old run completed dependency rebuilding and eventually FRP.Spec, reported
as 1885 seconds by Lake. It emitted the existing module-system import warning
for the Mathlib umbrella. The later compiler was on SquareKit.Temporal.Finite
when the final stop preflight inspected the process group. There were 275
completed project `.olean` files at the stopped boundary.

Only process group 69233 received SIGINT after checking its exact launcher,
working directory, old candidate SHA, clean checkout, and every group member's
workspace location. The record `1002-cba657b-interruption.json` preserves those
identities and signal time. The old log ends with check.py's KeyboardInterrupt;
there is no candidate success record. All recorded processes were confirmed
stopped before checkout changed. An earlier conservative descendant-list
preflight aborted before signalling; the final preflight enumerated the actual
matching process group.

The interactive session poll returned `Unknown process id 49524`. Therefore
its numeric wrapper exit status is unavailable and recorded as null, rather
than inferred as 130. The observed outcome is an intentional SIGINT
interruption with the retained traceback, not a successful or failed proof
audit. No proof failure or unexpected artifact-integrity rejection was observed
in that run. Its complete log remains `1002-candidate-cba657b.log`.

## New run and unchanged gates

After the old processes stopped, the clean detached validation worktree was
advanced to 777bab9. Completed ordinary build outputs were retained. The normal
guard handles missing traces from the unfinished build; no manual cache
substitution or cache fetch occurred. Source, toolchain, dependency and build
configuration pins remain unchanged except for the two committed Lean imports.

At 06:02:28 UTC, the same pinned Nix environment launched:

```sh
LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD
```

`1002-candidate-777bab9.run.json` records the complete command/environment
additions, its isolated process group and future exact subprocess return code.
A surrounding recorder writes that status independently of the interactive
session; it does not change the command or validation logic. The associated
`.log` is the full stdout/stderr stream. No other compiler is running for this
task. The new source-policy/coverage checks passed. The mandatory full build,
output guard, exhaustive audit, proof-audit regression, both independent review
axes and final candidate verification remain required. Preface, Perm and #1021
remain unaccepted, and Sort implementation remains blocked.
