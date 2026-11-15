# Checked temporal/evaluation imports and exact candidate restart

2026-11-02. New candidate: `de575a81266ac98194c7c5c83e91628098aac92e`.
The enclosing base remains `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Full scope:
12 files, 474 insertions, 4 deletions, no exclusions.

Local #1022 contributes only the two import headers described in its specification.
Both complete staged modules passed with unchanged mathematical bodies: Finite
with Fin.Basic/Sigma.Basic/Convert (52.538727s, exit 0), and Evaluation with its
existing relation import plus explicit core Omega (123.724885s, exit 0). Both
produced no diagnostics and their emitted import metadata matched. The initial
Finite attempt failed on the missing Sigma lemma; its evidence remains frozen.
All protected identities were unchanged, and no staging artifact entered a cache.
Exact integrated/source identities are in 1022-integration.json.

Finite alone would leave the Evaluation path to Mathlib.Tactic. Both headers
are therefore included together. Their project reverse-closure union contains
52 modules including the two roots. This is static dependency evidence, not a
controlled speedup or proof that all clients still elaborate.

The preceding bed44c1 run had no observed Lean error. It compiled Demand,
Temporal, TemporalCausality, TemporalPayload, Examples.FRPDemand and Temporal.Syntax,
but was deliberately superseded before completion. Root verified its recorded
process group 185670, leader command/start time, and every member's workspace
location, then sent SIGINT only to that group. The independently recorded raw
return code is -2; interactive session 98610 reported wrapper exit 130. Root
confirmed the entire group inactive before changing the isolated checkout.
The old log ends with KeyboardInterrupt. Its 288 completed project oleans remain
under the ordinary guard. No successful build, audit or acceptance is inferred.

The clean isolated checkout now runs the unchanged command:
`LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD`.
Its run record is 1002-candidate-de575a8.run.json, begun at
2026-11-02T07:07:57.238803+00:00; the adjacent log contains all output. Required full
coverage, guarded compilation, exhaustive audit, post-build proof-audit regression,
independent Standards/Spec assessment, and final candidate verification remain.
No fresh-mode trigger, dependency change, or stale-artifact evidence is present.
No chapter or cross-cutting ticket is accepted by this restart.
