# Isolated relative-model experiment

These files belong to the [#126 feasibility assessment](../../docs/research/relative-graph-model.md).
They are not library modules and are deliberately outside `SquareApplications`,
Lake's conaled targets and the repository's exhaustive `ProofAudit` roots.
They require the exact upstream checkouts listed in the assessment.
The [pin-alignment record](pin-alignment.md) verifies that the selected
ConLeche revision is newer than the release bundle and records the separate
ConRon port blocker.

Run from the conaled root:

```sh
direnv exec . bash experiments/relative-graph/reproduce.sh
```

Use `--conleche-only` to replay only the selected ConLeche route.

The script creates temporary pinned checkouts, builds the selected upstream
import closures and checks the adapter and inventories there. It changes no
main-project dependency. Builds may download the two Lean toolchains and
Lean4Lean's pinned Batteries dependency. Output stays in the printed temporary
directory. Review the axiom inventories: the Lean4Lean type-uniqueness diagnostic
is expected to contain `sorryAx`; it is not approved for use.

`GraphAdapter.lean` proves a conditional formula comparison in ConLeche's
set-valued denotation, using explicit `SetTheory`, `Model` and primitive-law
parameters. It does not instantiate `model_exists`, establish checker
acceptance, translate the native emitter, or provide an unconditional model.
`ConLecheAudit.lean` inspects the independently built model theorem and semantic
lemmas. `Lean4LeanAudit.lean` records the selected alternative's clean and
admitted declarations separately. The observation record is in
[evidence.txt](evidence.txt).
