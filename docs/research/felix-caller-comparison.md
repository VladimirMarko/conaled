# Matched categorical caller comparison

Both independent authors checked all three tasks from
[#25](https://github.com/VladimirMarko/conaled/issues/25): transported laws,
composition of interpretations, and a general comma caller. Neither attempt
exposed a missing generic capability in this sample. This is evidence for the
specified natural-matrix examples, not library-wide parity or a ranking of
language productivity.

The [frozen protocol](felix-caller-trial-protocol.md) defines the common contract.
The [evidence directory](../../experiments/felix-caller-comparison/) retains
source, failed snapshots, diagnostics, author reports, environment identities,
launch records and the independent prelaunch review. Production APIs were not
changed to improve the results.

## Baselines and method

Lean uses `3c064b11a5812e38c317601473e6897f65ce2a32`, advancing the issue's
original baseline to include completed #8 and #24. Felix uses
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. The
[environment manifest](../../experiments/felix-caller-comparison/environment.json)
pins Lean 4.35.0, Mathlib, Agda 2.8.0, standard library 2.3 and both Nix locks.
Neutral source checks preceded launch. Fresh Agda checking needed a writable
copy of the pinned standard-library sources because Nix's store is read-only;
the unsuccessful provisioning commands and successful check are retained.

Two fresh-context agents received the same contract and budget, their own pinned
public library sources and examples, and route-specific environment instructions.
They could not read each other's trial or receive mathematical/API coaching.
Both used inherited model configuration without overrides. The orchestration API
does not expose its resolved model/version identity; the launch manifest records
this reproducibility limitation. One attempt per route supports no population
estimate. Reading and search were summarized rather than exhaustively logged;
every trial-source checker invocation has a source snapshot and result.

Each route had a prospective cap of 60 feedback rounds and 180 active minutes.
Both finished below the caps with no waiting exclusions or coordinator coaching.
Their sources were frozen before coordinator reproduction. These are observed
attempts with access to existing libraries, not unaided reconstruction exercises.

| Task | Lean first/full outcome | Felix first/full outcome | Conclusion on the common contract |
|---|---|---|---|
| Interpretation and transported laws | Round 1 failed; round 2 passed | Core passed round 1; full package failed round 2 and passed round 3 | Both supported, with disclosed equality/coordinate encodings. |
| Composition | Round 3 passed first attempt | Round 4 failed; round 5 passed | Both reused established maps and preservation packages. |
| General comma caller | Round 4 failed; round 5 passed | Round 6 failed; round 9 passed | Both retained distinct sources, nonidentity connectors, composition order and arbitrary-dimension products. |

Recorded active elapsed time to the successful final check was approximately
376 seconds for Lean and 490 seconds for Felix. Lean's receipt time was a
conservative approximation preceding its first clock reading; Felix used its
first clock observation. These timings and the 5/9 round counts describe the
attempts. They do not isolate library interface quality, author variation,
checker cost or host scheduling, and are not an elegance score.

## Mathematical scope and local work

Both source categories have natural-number dimensions and natural-number
matrices, interpreted by finite-sum action. The intermediate arrows are arbitrary
functions between coordinate spaces. Its product object is dimension addition;
the final type/function category uses ordinary pairs. Split/join comparisons
and both inverse laws establish non-strict product preservation. Matrix semantic
equivalence compares actions, without requiring reflection to matrix entries.

Lean uses `Fin n → Nat` and Mathlib matrices. Function extensionality connects
pointwise observations to function equality. Felix uses inductive `Vec Nat n`
and vectors of rows, with pointwise equality on function arrows. Its checked
lookup/tabulation roundtrips connect that permitted equivalent encoding with
finite coordinate functions; it introduces no function-extensionality postulate.
Both concrete trials stay at their selected small universe and scalar type.
They do not test all universe levels, scalars or categorical structures.

| Responsibility | Lean caller | Felix caller |
|---|---|---|
| One-time arithmetic and representation | Mathlib supplies matrix identity/action and multiplication/action facts. The caller supplies dimension products, coordinate selection, split/join and local product proofs. | The caller supplies recursive dot product, matrix action/composition and local arithmetic proofs, reusing standard-library Nat/Vec facts and conversion roundtrips. |
| Interpretation packages | `RawMap`, `MapLaws`, `TerminalMap`, `ProductMap`, comparisons and semantic congruence. | `Homomorphism`, `H-equiv`, `CategoryH`, `ProductsH`, `StrongProductsH`, `CartesianH`, and explicit instances. |
| General laws inherited | `transportLaws` and `transportCongr` for category, terminal and product structure. | `MakeLawful.LawfulCategoryᶠ` and `LawfulCartesianᶠ`. |
| Composite interpretation | `RawMap.comp`, `ProductMap.comp`, their laws and composed comparisons. | `_∘H_`, `_∘-CategoryH_`, `compose-ProductsH`, `_∘-CartesianH_`; the inverse comparison reuses `dimStrong` because the first comparison is identity. |
| Comma consumer | General `Comma` operations, semantic projections and `CommaProducts`. | General `Felix.Construct.Comma` operations, `f₁`/`f₂`/`↻` projections and `comma-products`. |

The arithmetic difference concerns available corpus and representation as well
as interfaces; it is not evidence that one generic transport construction is
weaker. Both authors charged this setup once. Neither reimplemented a missing
generic categorical construction. Task 2 adds composition and observations,
without repeating matrix arithmetic. This particular chain has one identity
comparison and one non-strict comparison; it does not test composition of two
independently non-strict comparisons.

The comma task uses matrix and type/function sources into a common function
category, with coordinatewise doubling as connector. The caller proves shear
and swap action and commutation for every input. Both composition orders are
formed by public comma operations, and the numerical observations distinguish
`(1,2) ↦ (2,3)` from `(1,2) ↦ (3,1)`. Product connectors and projections quantify
over arbitrary dimensions. Lean additionally exercises general fork beta/eta
laws; that extra evidence is not used to score Felix against a stronger task.

## Caller knowledge, repairs and locality

[Lean's report](../../experiments/felix-caller-comparison/lean/report.md) and
[Felix's report](../../experiments/felix-caller-comparison/felix/report.md)
inventory declaration names, dependencies, setup and repairs. Lean's failures
were a missing dimension binder, simplifier visibility through a map wrapper,
and concrete finite-index numeral elaboration. Felix's failures concerned
implicit summand inference, an ambient map instance, hidden universe/constructor
arguments, arithmetic rewrite steps and recovering product component objects.
All failed snapshots remain available. These are observed caller obligations;
this sample does not establish which deserve a production interface change.

Both authors had to learn raw operations, semantic equality, map laws, product
comparisons and general comma packaging. Felix's instance-driven field access
sometimes needed explicit ambient data. Lean's wrappers sometimes needed local
unfolding or index annotations. Neither route reconstructs the internal proof
of general category or comma laws to obtain the task's semantic conclusions.
The terminal/product and comparison setup is explicit caller data in both.

Encoding locality is supported by actual dependencies. Coordinate representation
and local action/projection proofs change together; concrete shear/swap and their
numeric observations also depend on the encoding. Map-law transport and task-2
composition consume packaged laws, while generic comma composition consumes the
resulting interpretation packages. The explicit product observations still name
split and doubling. A representation change does not leave all caller text
unchanged, and neither author claimed that stronger result.

No demonstrated missing-power or avoidable-work gap warrants a new issue from
these attempts. Existing #235 remains the owner for broader usability and
preservation assessment. Completing this evaluation establishes these three
supported examples, leaving unexamined Felix capabilities and library-wide
elegance open. The full-section and Agda-like surface experiments remain separate.

## Reproduction and acceptance

[Lean final source](../../experiments/felix-caller-comparison/lean/final.lean)
includes an isolated copy of the pinned proof auditor with one module-selection
adaptation: include the current invocation module. Coordinator reproduction of
the frozen hash passed and audited 507 kernel-safe declarations, including
203 theorem declarations, with only `propext`, `Classical.choice`, `Quot.sound`.
The adaptation and helper cost are disclosed; this is an experiment audit,
not a claim that these files are imported into the production entrypoint.

[Felix final Task3](../../experiments/felix-caller-comparison/felix/Task3.agda)
imports Task2, Task1 and Core. All four use `--safe --without-K`. Coordinator
fresh `--ignore-interfaces` reproduction passed for the same frozen hashes,
including rechecking dependencies. The
[reproduction receipt](../../experiments/felix-caller-comparison/reproduction.json)
records both exact commands and full-log hashes. Dependency
`UnsupportedIndexedMatch` warnings remain in the retained log; the safe caller
modules checked successfully. Independent Standards/Spec acceptance is recorded
by the enclosing review loop.

To reproduce, use separate worktrees at the pins above and their declared Nix
shells. Build Lean's `SquareKit.CommaProducts` and `SquareKit.FunctionCategory`
in that baseline, then run `lake env lean` on the retained final source. For
Agda, use a writable copy of the pinned standard-library 2.3 source and invoke
`agda --no-libraries --ignore-interfaces` with include paths for that source,
the pinned Felix `src`, and this evidence directory's `felix` subdirectory,
checking `Task3.agda`. The exact executed commands, source hashes and diagnostics
are in the manifests, attempt logs and reproduction receipts. Preserve failed
attempts as evidence; only the final files are expected to check successfully.
