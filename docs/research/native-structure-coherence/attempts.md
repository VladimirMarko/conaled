# Native structure coherence: retained resource experiments

These probes accompany #687. They preserve failed encodings and the checked
alternative used in the implementation. They are not mathematical separating
instances. The Lean toolchain is the repository's pinned Lean 4.35.0.
The primitives imported by `CartesianCore` are unchanged from
`17f394859ffdf6a449c5deb6cefa56a89b78e883` (#680).

| Probe | Observed result | Decision |
| --- | --- | --- |
| `CartesianStage2` | The sequential map-path comparison exceeded a 10-second wall limit. Explicit carrier type arguments alone also exceeded that limit. | Preserve the statement and move horizontal composition into a generic helper. |
| `CartesianStage2Horizontal` | Passed at default limits; a separate repeat completed in about one second, including the command wrapper. | Use `MapPath.horizontal`, whose proof is checked with arbitrary maps before specialization to selected `ua`. |
| `ExampleCanonicalExplicit` | The original-model integer inverse comparison using `selectedInverseEquivalence` exceeded a 30-second wall limit, even with explicit carrier-code arguments. | The consumer supplies a complete inverse witness from its inverse isomorphism. The general `inverseWith` and `inversion` interfaces still accept any supplied complete witness for the selected inverse map. |
| `ExampleFirstSubstitution` | The direct interval-projection specialization exceeded a 15-second wall limit. | Package the unchanged two whole paths and their comparison with the existing `PathData` interface before specializing the lawful fillers. The final complete example module built in 921 ms. |

The original model retains its general `Equivalence.inverse` constructor using
`selectedInverseEquivalence`. The failed consumer specialization does not refute
that construction. The Cartesian consumer proves `Selected.inverse_ofIso` and
transports its supplied inverse witness along that equation; it does not ask
Lean to rediscover the equation by unfolding the entire construction.

The Cartesian `wholeComparison` declaration exceeded the default 200,000
heartbeats and passed with a local 400,000-heartbeat setting. Other reductions
were resolved by named equations, explicit map endpoints, or proofs parameterized
by arbitrary lawful fillers. No recursion-depth override is introduced. These
are local resource decisions, not evidence of a general productivity improvement
or an upstream Lean defect.

## Reproduce the paired map-path probes

The `.lean.txt` files are exact saved probe sources. Their extension keeps
experimental declarations out of the library build and proof audit. Run from
the repository root with the development environment available:

```bash
trial_dir=$(mktemp -d)
for name in CartesianCore CartesianStage2 CartesianStage2Horizontal; do
  cp "docs/research/native-structure-coherence/$name.lean.txt" "$trial_dir/$name.lean"
done
direnv exec . lake env lean -R "$trial_dir" -o "$trial_dir/CartesianCore.olean" "$trial_dir/CartesianCore.lean"
direnv exec . lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; timeout 10 lean "$1/CartesianStage2.lean"' bash "$trial_dir"
direnv exec . lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; timeout 10 lean "$1/CartesianStage2Horizontal.lean"' bash "$trial_dir"
```

The saved core has the measured local heartbeat setting. Neither paired probe
changes it or raises a resource budget. Exit status 124 means the wall limit
expired; an empty log alone says nothing about success. Wall limits depend on
the machine and concurrent load, so remeasure rather than treating the observed
threshold as a theorem.

For the canonical inverse specialization, copy
`ExampleCanonicalExplicit.lean.txt` to a temporary `.lean` file and run
`direnv exec . timeout 30 lake env lean PATH_TO_FILE` after building
`SquareKit.Internal.Cubical.NativeStructureCoherence`. This probe defines its
own integer consumer and does not import the final example module.

The `ExampleFirstSubstitution.lean.txt` probe can likewise be copied to a
temporary `.lean` file and run with a 15-second wall limit after building both
coherence modules. Its statement is unchanged by the packaging used in the
final consumer; the paths and their homotopy remain available as data fields.

## Source identities

| Source | SHA-256 |
| --- | --- |
| `CartesianCore.lean.txt` | `44764625197cd2c6f8ca8844172a5a2b1a97cf6cfaa291f1f145762ab61ab51a` |
| `CartesianStage2.lean.txt` | `df8b95f35372929154bdfb49fcce2e3e60fc6ab7529e06dbc668bc5ed3c6998a` |
| `CartesianStage2Horizontal.lean.txt` | `2bb9313f0780df80316ba4bec1941e508f9fc53938bda80f1ec14894f8cd3d55` |
| `ExampleCanonicalExplicit.lean.txt` | `68b11cf9806ce79c65507ac42d9fd755fcd379bfb91e49af1327a4eea9cea181` |
| `ExampleFirstSubstitution.lean.txt` | `702ca6436f29d6a8e4c301176dfa28a45c564c08ddce34d1963b22bd46d257df` |
