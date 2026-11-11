# Lean caller trial at baseline 3c064b11

All three tasks checked under Lean 4.35.0. The final independent source is
`final.lean`, SHA-256
`14251b8e1ad49b4d310ef65da4c766df613410e2599f284513b693d185872669`.
The protocol was read at commit `71bf7817`; production sources were unchanged.
The isolated baseline checkout remained clean.

The source was frozen after round 5 passed at 2026-11-11 15:25:36.411594 UTC.
The recorded receipt time is a conservative approximation, 15:19:20 UTC;
the first actual clock reading was 15:19:26 UTC. Thus active elapsed time to
successful checking is 376.411594 seconds using that approximation. No time was
excluded. Reporting and the compiler-version query followed source freeze.
This is one agent attempt, not a human-productivity measurement or a comparison
with the other route. The coordinator records the agent/model selection identity.

| Task | First attempt | Final attempt | Assessment |
| --- | --- | --- | --- |
| 1: interpretation and transported laws | Round 1 failed | Round 2 passed | Supported on the examined contract |
| 2: composition | Round 3 passed | Round 3 passed | Supported on the examined contract |
| 3: general comma caller | Round 4 failed | Round 5 passed, including audit | Supported on the examined contract |

`attempts.jsonl` records every trial-source checker invocation before execution,
its frozen snapshot hash, task, start/end timestamps, and exit status. The exact
snapshots and full diagnostics are `round-01.lean` through `round-05.lean` and
corresponding `.log` files. `task1-final.lean`, `task2-final.lean`, and
`task3-final.lean` retain the task boundaries. The last is byte-identical to
`final.lean`. Read/search work is summarized in the provenance event rather than
logged as an exhaustive shell transcript. That is a logging limitation; all
actual trial-source checker invocations are recorded individually.

## Checked mathematics and statement review

Task 1 uses exactly natural-number objects, `V n = Fin n → Nat`, and arrows
`Mat n m = Matrix (Fin m) (Fin n) Nat`. `raw.comp g f` is `g * f`, so the right
argument runs first. The identity is the matrix identity. `mt` chooses dimension
zero and its unique empty-row matrix. `mp` chooses dimension addition, explicit
coordinate-selection matrices, and concatenated rows using `Fin.addCases`.
These are raw data, not an assumed lawful matrix category.

`interpret` maps each matrix to `Matrix.mulVec`. `coord` has all functions
between the coordinate spaces as arrows. Its selected product still has object
`n + m`. `types` maps that object to `V (n + m)`, with comparison `split` and
inverse `join`, rather than replacing it by a pair. `split_join` and `join_split`
prove the two inverse laws for arbitrary dimensions, including zero. The terminal
comparison connects the empty coordinate space with `PUnit`.

`ce` is induced equality of functions through `types`. `semantic` is induced
through `interpret`; `semantic_iff` explicitly proves that it means equality of
every output coordinate for every input vector. Lean function extensionality is
used to pass between pointwise equality and function equality. No matrix-entry
reflection is required or used. This encoding uses Lean extensionality; it should
be reported separately from any route retaining pointwise setoid equality.

`interpret_laws` discharges identity and composition by pinned Mathlib's
`Matrix.one_mulVec` and `Matrix.mulVec_mulVec`. Projection and pairing preservation
are finite-sum/coordinate proofs. General category laws, composition congruence,
terminal uniqueness, product congruence, and product beta/eta are then obtained
through `RawMap.transportLaws`, `RawMap.transportCongr`,
`TerminalMap.transportLaws`, `ProductMap.transportLaws`, and
`ProductMap.transportCongr`. The coordinate category also obtains those laws
through its interpretation into the baseline function category. The assumptions
are established packages, not extra premises hiding the desired laws.

Task 2 forms `interpret.comp types`, `ProductMap.comp matrixProducts typeProducts`,
and the corresponding terminal comparison. Public `comp_laws`, `map_laws`, and
comparison composition prove the preservation and inverse laws. No additional
matrix arithmetic is proved. `composite_action` identifies arbitrary matrix
application with the finite sum; `composite_composition` establishes the chosen
order; `composite_pair`, `composite_first`, and `composite_second` state its product
observations through the selected split/join comparison.

Task 3 uses matrix operations as the left source and the baseline type/function
category as the right source. The common target is the type/function category.
The left interpretation is the task-2 composite; the right interpretation is its
own identity map on the function category. `object n` has connector
`double x i = 2 * x i`. The two sources remain distinct. An identity interpretation
on the right does not replace that connector by an identity arrow;
`connector_nonidentity` checks a one-coordinate witness explicitly.

`shearMatrix` and `swapMatrix` are actual natural matrices.
`shear_action`/`swap_action` prove their action on every two-dimensional vector.
`shear_double`/`swap_double` prove commutation with the connector for all inputs.
`L` and `R` package those facts as general comma arrows. `RL` and `LR` use public
comma composition. `leftProjection`/`rightProjection` use public comma projections;
`RL_left`, `LR_left`, `RL_right`, `LR_right`, and `RL_square` state their matrix,
function, and commuting-square semantics. The retained input is `(1,2)`.
`RL_observation` proves `(2,3)` and `LR_observation` proves `(3,1)` through those
universal projection theorems, so the examples distinguish composition order.

`commaProducts` uses the public general comma product constructor with the
established left comparison and the right identity comparison. Its connector on
`object n` and `object m` is proved to return the doubled split coordinates.
Both projection-square statements quantify over arbitrary `n`, `m`, and input
vectors. `fork_first`, `fork_second`, and `fork_eta` use the public comma product
laws for arbitrary comma objects and arrows, including arbitrary connectors.
Their equality is componentwise semantic equality on matrices and ordinary
function equality on the right, exactly the selected source equivalences.

Statement review found no weakened contract, circular hypothesis, additional
axiom, or task-specific assumption. The finite numerical cases supplement the
universal statements. The result establishes this finite natural-matrix caller
contract, not capabilities for every categorical structure or scalar system.

## Caller work, provenance, and repairs

The trial's mathematical declarations are newly written instantiations using
public baseline APIs. Public examples were inspected: `MatrixCategory`,
`MatrixDoubling`, and `Examples/MatrixCompilerPreservation`. Their matrices use
finite coordinate types and different comparison/connector data; none was
copied as a solution to the trial. `FunctionCategory` supplies the target packages
and provides the transport pattern. `Category`, `CategoryMap`, `CartesianMap`,
`Comma`, and `CommaProducts` supplied the inspected interfaces. Mathlib matrix
multiplication supplies arithmetic facts; `Fin.addCases`, finite sum simplification,
and `fin_cases` supply coordinate manipulation. No other route output, outside
mathematical assistance, or delegated author was used.

One-time setup in task 1 comprises the two raw categories, three chosen terminal
and product structures, two interpretations, their semantic equivalences,
comparisons, local preservation facts, and the transported laws. This is charged
once. The first task source has 132 lines including imports and whitespace.
Task 2 raises the source to 173 lines, adding 41 lines for composition and its
observations. The final file has 423 lines, of which the mathematical trial ends
at `end Trial`; the remainder is an isolated audit adaptation. These are descriptive
counts, not elegance scores. No missing generic mathematical infrastructure was
implemented by the caller.

Round 1 exposed an omitted dimension binder in `interpret_laws` and simplifier
visibility of the `types.map` wrapper in the matrix product proofs. Round 2 adds
`intro n` and unfolds `types` in those local proofs. Round 3 passed without repair.
Round 4 passed the general comma constructions and proofs but rejected numeral
elaboration in the two concrete observations: typeclass search did not unfold the
object/projection wrappers to expose `Fin 2`. Round 5 explicitly annotates those
indices and adds the isolated audit. Two unused-variable linter warnings for
comparison dimension names remain. They are preserved rather than changing
source after completion.

Changing the coordinate encoding affects `V`, `Mat`, raw matrix identity/composition
indexing, `split`, `join`, coordinate and matrix product/terminal data, and the
local arithmetic/coordinate preservation proofs. The concrete shear/swap matrices,
input vector, and action proofs also depend on `Fin 2`. By their actual dependencies,
transported law declarations use the interpretation packages, while task-2
composition uses only public map/comparison composition. General comma packaging
uses the composed packages. The explicit product connector and numerical
observations refer to `split`, `double`, and the concrete coordinate functions.
No claim is made that changing the encoding would leave all source text unchanged.

## Environment and validation

The baseline commit is `3c064b11a5812e38c317601473e6897f65ce2a32`. The compiler
query reports Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The four environment-file hashes
match the frozen manifest. The pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The first focused dependency build failed because the isolated `.envrc` was
blocked. After reading its contents, `direnv allow` repaired environment access.
`direnv exec . taskset -c 3 lake build SquareKit.CommaProducts SquareKit.FunctionCategory`
then succeeded using private project outputs and linked pinned package outputs.
Both logs are retained. No project output was copied from another worktree.
No clock exclusion or coordinator intervention was needed. Dependency-only build
commands are recorded separately from trial-source feedback rounds.

Every trial round ran from the assigned baseline checkout with:

```sh
direnv exec . taskset -c 3 lake env lean /tmp/conaled-wave-20261111/25-authors/lean-output/round-NN.lean
```

The final reproduction command, for the coordinator, is:

```sh
direnv exec . taskset -c 3 lake env lean /tmp/conaled-wave-20261111/25-authors/lean-output/final.lean
```

The final file incorporates the pinned `ProofAudit.lean` implementation after its
imports/documentation. Its sole algorithmic adaptation is a local module predicate
that also includes `env.mainModule`, because an isolated Lean invocation names the
current module `_stdin`. The trial directly imports `Lean.Util.CollectAxioms` and
`Lean.DeclarationRange`; it does not import the entire production entrypoint.
This adaptation is validation tooling, not mathematical infrastructure. The audit
checked 507 kernel-safe declarations, 203 theorem declarations, and seven project
modules. The current module contributes 154 logical declarations and 76 theorem
declarations, including the audit itself and generated declarations. The reported
transitive axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
The pinned source scanner (`scripts/check.py`'s `executable_source` and `FORBIDDEN`)
also passed on the final source.

This is an isolated experiment, not an integrated production change. The full
repository `./check.sh --candidate` acceptance was not run and is not claimed.
Coordinator reproduction and independent Standards/Spec review remain separate
from the frozen independent author attempt. No demonstrated generic capability
gap was found requiring a proposed follow-up; this does not establish library-wide
capability parity or a comparative productivity conclusion.
