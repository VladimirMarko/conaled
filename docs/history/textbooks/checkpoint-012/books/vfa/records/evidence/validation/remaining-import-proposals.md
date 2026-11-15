# Remaining umbrella imports: bounded read-only proposals

Independent investigation by reuse_survey, 2026-11-02 07:54–07:59 UTC.
Root read both complete proposed modules. Neither investigator changed source,
cache, configuration or process state during this source-graph investigation.

There are eleven direct Mathlib.Tactic imports and no direct Mathlib import
in the production globs. Counts below resolve project/package source imports
and exclude compiler-distribution Init, Lean, Std and Lake modules. There were
no unresolved package imports. Artifact presence is not acceptance evidence.

| Root | Reverse project closure | Completed artifact sets | Still-uncompiled modules losing their only umbrella path | Proposed source closure |
| --- | ---: | ---: | ---: | ---: |
| Applications.Durability.Retention | 11 | 0 | 8 | 3124 to 605 |
| Applications.Orbifold.ProjectiveMotion | 30 | 6 | 22 | 3168 to 2401 |

Reverse closures include the root and the two aggregate modules ProofAudit and
SquareApplications. The aggregate modules retain other umbrella paths.

## Retention: selected for a bounded experiment

The whole module's specialist tactics are split_ifs and omega. Replace only its
Mathlib.Tactic import with Mathlib.Tactic.SplitIfs and Lean.Elab.Tactic.Omega.
Unchanged Mathlib.Data.List.TakeDrop publicly imports Tactic.Common, retaining
Aesop used by RetentionClients. The Mathlib portion falls from 2837 to 330.

Retention, Banks, Service, Machine, Ownership, Resources, Clients and Summary
would lose their only umbrella path, and all lacked completed artifact sets.
Examples.RetainedHistory also inherits DiagnosticGraph and retains that path.
The exact source hashes and all experiment requirements are in
../specs/1024-Retention-imports.md.

## ProjectiveMotion: deferred, not authorized for a compiler or edit

The bounded proposal replaces Mathlib.Tactic by Mathlib.Tactic.Linarith and
Mathlib.Tactic.FieldSimp. The whole module uses exact_mod_cast, nlinarith and
field_simp; exact_mod_cast is a pinned core macro in Init/TacticsExtra.lean.
Its proposed closure retains the obvious inspected downstream tactics:
fin_cases/ring_nf, linear_combination, module, fun_prop, positivity, norm_num,
ring, convert and Aesop. The Mathlib portion falls from 2883 to 2120.

No independent umbrella survives in the 28 non-aggregate reverse modules.
Six already have artifact sets and would need rebuilding: ProjectiveMotion,
StandardForm, Disk, Pose, ConnectionAssessment and Linear.Similitude.

Current SHA256:
76fd6a04ad9c3b283888f7c44b99237339f5f516acb9dedefe98cbe0db44c0c5

In-memory proposed SHA256:
d0e0920d166555216764e3a20d6c8f3c26ea15415b1072da527654894d491ae3

Root defers this proposal: its smaller reduction, six completed invalidations
and larger client scope make it less compelling than Retention. No focused
compiler or source modification for ProjectiveMotion is authorized now.

## Interpretation

Static source closure and explicit tactic-provider inspection do not establish
unchanged elaboration, ambient simp/instance availability, downstream success,
or a controlled performance improvement. Only the ordinary candidate gates can
establish compatibility after any selected edit. No chapter is accepted here.
