# Bounded #107 resumption probes

These are isolated comparison callers, not a production API or a successful
repair freeze. The [assessment](../../docs/research/dependent-congruence-resumption.md)
records their scope, statement review and proposed migration decision.

- `FixedTemplates.lean` checks the existing generated rules on actual dependent
  concatenation arguments, transport, a dependent extension and fresh raw syntax.
- `GuardedComparisons.lean` checks the newer source-only fresh-operation and
  finite-tail command comparison. Its concat recipe is not the legacy recipe.
- `FreshAnnotation.lean.txt` is intentionally rejected. It asks whether `rfl`
  proves the legacy substituted-versus-fresh annotation equation. Its failure
  establishes only that this proof attempt does not work.
- `fresh-annotation-diagnostic.txt` retains that compiler diagnostic.
- `*-axioms.txt` retain `#print axioms` output for every named probe declaration.
  These inspections do not substitute for the full acceptance audit.

Use the repository's pinned environment and isolated local project outputs:

```sh
direnv exec . lake build SquareKit.Internal.PathTransport.TransferFrame SquareKit.Internal.PathTransport.ConcatenationCongr SquareKit.Internal.DependentJudgments.TransportReindexing SquareKit.Internal.DependentJudgments.Templates
direnv exec . lake env lean experiments/dependent-congruence-resumption/FixedTemplates.lean
direnv exec . lake env lean experiments/dependent-congruence-resumption/GuardedComparisons.lean
```

The following command must exit unsuccessfully with the retained `rfl` failure;
its result is never included in successful source or proof-audit claims:

```sh
direnv exec . lake env lean experiments/dependent-congruence-resumption/FreshAnnotation.lean.txt
```

To reproduce the axiom inspections, append `#print axioms` commands for the
fully qualified declaration names printed in each retained output to a temporary
copy of the corresponding source, then check that copy with `lake env lean`.
The sources remain outside the normal integrated import closure. A successful
#107 freeze still requires its full mathematical acceptance, integration and
fresh validation, independent review and a separate unprepared #108 theorem.

## Guarded endpoint diagnostic

After building `SquareKit.Internal.DependentJudgments.LeftAssociativity`, run:

```sh
direnv exec . lake env lean experiments/dependent-congruence-resumption/GuardedWrongEndpoint.lean.txt
```

This must fail on `hq`: the caller supplies `q : x = z` where the composable
triple requires `q : y = z`. `GuardedWrongEndpoint.diagnostic.txt` retains that
output. This failing source is not an integrated theorem. Successful arbitrary
callers and the later acceptance boundary are in the
[guarded repair report](../../docs/research/guarded-dependent-authoring-repair.md).
