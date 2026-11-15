# Actual random quicksort growth: source handoff

Exact candidate: `08a1e78d6becc713256d245206ef163f9eb55a0a`.
Exact parent: `c0440a99c2a503b7816a44367f7e4168378dbbf1`.
Branch: `work/fdsa-ch02-random-pivot`.
Commit: `feat(fdsa): connect actual random quicksort mean growth (#174)`.

The author worktree is clean. This commit adds exactly
`Applications/Resources/RandomQuickSortGrowth.lean` and
`Examples/RandomQuickSortGrowth.lean`, with 418 total lines. No prior source,
root import/map, dependency pin or existing handoff/control file was edited.

## Exact source identity

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| Resource | 203 | 9896 | `2b8bf7b4820790edaaa5726efb8e8bd8bccd3a30cb30388148d95bba00e63674` |
| Examples | 215 | 9959 | `2d173d7572ae76395c3779c216ea43d21719ff1774f6a7f21c68a5677b511a16` |

The source contains all 17 approved resource theorems and 14 approved connected
example theorems. There are no private declarations. The complete source
inventory records every public header. The complete statement assessment
records the intended and actual contract of every theorem and covers every
proof body. I read all 418 source lines and the full generated inventory. No
concrete mathematical source-contract finding remains in the author's
assessment. Elaborated statements have not yet been inspected.

## Implemented source connection

The first theorem applies the numerical recurrence solver directly to actual
`sizeMean_zero` and actual `sizeMean_recurrence`. The new harmonic result then
uses the actual input-to-size equality under `(xs.map key).Nodup`. It imposes
only an order on keys, with independent payload and key universes. No numerical
recurrence is assumed for the algorithm.

The literal harmonic sandwich and doubled logarithmic constants come from the
existing comparison of observations of the same run. The actual exercise and
append-inclusive means have binary-log constants 32 and 64 from size two.
There are natural-log scalar bounds and standard `Asymptotics.IsBigO` results.
The four arbitrary-family statements allow an independent index universe,
arbitrary filter, eventual mapped-key distinctness and Tendsto of actual list
length atTop; their comparison functions use that actual length.

Consequential examples include Empty payloads, arbitrary singleton tags,
positive zero/one costs that exclude all-size pure n-log-n bounds, the actual
13, 71/3, 109/3 and 253/5 means, arbitrary lists of each length, function-valued
payload tags, and a family with size n+2. Equal-key examples retain both actual
quadratic means. At size 256 those means are 131585 and 132353, while the
distinct-key scalar right sides would be 65536 and 131072; both inequalities
fail. The example explicitly retains distinct raw payloads, so payload Nodup
cannot replace mapped-key Nodup. It makes no general non-Big-O claim from a
single counterexample.

## Validation and continuation

This is an uncompiled source candidate. The only local check was the meaningful
staged `git diff --cached --check`, which returned exit0 with an empty log.
No author compiler, Lake/check/audit process, cache operation or child agent was
started. The author worktree has no `.lake` directory.

The source dependencies are exactly the coordinator-aligned rank, mean and
numerical files recorded in `alignment-result.json` and `author-start.json`.
Their source assessments do not imply dependency compiler/acceptance results.
At the last supplied coordinator report, their central candidate was immutable
`c0440a99` in live attempt5; actual terminal and diagnostic evidence remains the
coordinator's responsibility. Any actual dependency or new-source diagnostic
takes priority and requires a separately recorded proof-only repair.

The exact harmonic equality excludes sampler implementation, random bits,
index access/pivot lookup/removal, allocation and physical runtime beyond the
specified tariff. The literal bound adds the existing right-associated append
observation and no additional pivot overhead. The distinct deterministic
first-pivot/uniform-input expectation remains mandatory. Full frozen Chapter 2
scope and all full-book obligations are retained.

The accepted Chapter 1 state is unchanged. This handoff supplies no foundation
or Chapter 2 acceptance. Root compilation, all 31 explicit type inspections,
the applicable full immutable-candidate check/audit, both independent review
axes and immediate candidate verification remain required. Every previous
failure and its terminal record remains preserved.

After closing the adjacent candidate identity, HOLD all source, ref, control
and provenance writes pending coordinator diagnostics, checkpoint capture or
explicit next release.
