# conaled

A Lean library for compositional verified programs and mathematics, extending
Conal Elliott's work on categorical compilation. It connects mathematical
specifications to implementations, analyses, and alternative representations
through reusable operations and preservation laws.

The aim is to build a useful library: prove the local laws once, then reuse them
in compilers, algorithms, stateful systems, and mathematical constructions.
A compiler target may be executable code, a cost analysis, an enclosure, or
another mathematical interpretation. Each target states what it preserves.

The longer-term [language direction](docs/language-direction.md) is to make the
mathematical setting a parameter of programming and proof. The current library
provides concrete languages, models, and transport constructions toward that
goal. It builds on Lean and Mathlib; Felix is an architectural and mathematical
reference.

## Finding your way

Start with a checked client close to the problem you want to solve:

| Task | Example and reusable API |
|---|---|
| Compile a scalar map, sum its results, and repair the sum after input changes | [Mapped aggregates](Examples/MappedAggregate.lean), using [MappedAggregate](Applications/Incremental/MappedAggregate.lean). Includes downstream composition and complete modeled repair-versus-recomputation costs. |
| Compare native and compiled finite loops | [Measured loops](Examples/MeasuredLoop.lean), using [MeasuredLoop](Applications/Resources/MeasuredLoop.lean). This bounded experiment proves matching independent sum specifications and counts guard/body work. |
| Reuse a table client across representations | [Total tables](Examples/TotalTables.lean), using [TotalTable](Applications/Search/OrderedMap/TotalTable.lean). Functions, association lists, and valid raw trees share lookup-after-write laws. |
| Reuse queue behavior and account for persistent branches | [FIFO clients](Examples/AbstractFIFO.lean), [resource contracts](Examples/FIFOContracts.lean), and [persistent clients](Examples/PersistentFIFOClient.lean). |
| Connect incremental updates, stack execution, and interval analysis | [ArithmeticPipeline](Examples/ArithmeticPipeline.lean). |
| Execute finite representation changes justified by native univalence transport | [ExecutableUnivalence](Examples/ExecutableUnivalence.lean), using [ExecutableTransport](Applications/Representations/ExecutableTransport.lean). |

Follow an example's imports to its reusable definitions. Import those modules
in a focused client; [SquareApplications.lean](SquareApplications.lean) is the
aggregate public entrypoint for the integrated library.
[APPLICATIONS.md](APPLICATIONS.md) explains selected compiler applications and
compositions in more detail.

## What is in the library

| Area | Capabilities and entry points |
|---|---|
| Compilation and preservation | Exact and relational squares, typed first-order and higher-order compilers, structure-preserving maps, and law transport. Start with [Compiler](Compiler.lean), [FirstOrder](FirstOrder.lean), and [relations](SquareKit/Relations.lean). |
| Numerical and symbolic interpretations | Analytic automatic differentiation, polynomial derivative towers, scan and FFT, matrices, interval enclosures, language derivatives and parsers, and circuit timing. See [application contracts](APPLICATIONS.md) and [FFT optimality examples](Examples/FFTUnitaryOptimality.lean). |
| Incremental computation and resources | Retained-state repairs, shortest-path updates, measured execution, potential accounting, and representation-dependent costs. See [mapped aggregates](Applications/Incremental/MappedAggregate.lean), [incremental search costs](Examples/IncrementalSearchCosts.lean), and [resource composition](Examples/Resources.lean). |
| Algorithms and data structures | Sorting, selection, trees, maps, queues, sequences, and dynamic programming, including textbook reconstructions. Shared clients cover [sorting](Examples/TextbookSorting.lean), [maps](Examples/TextbookMaps.lean), [sequences](Examples/TextbookSequences.lean), and [tree tariffs](Examples/TextbookTreeTariffs.lean). |
| Internal languages and model transport | Dependent fragments, logical interpretations, sheaf/presheaf models, groupoid transport, and construction/observation compatibility. Start with [SquareKit/Internal](SquareKit/Internal/), [dependent-source examples](Examples/DependentSource.lean), and [the contract inventory](docs/research/preservation-contract-inventory.md). |
| Cubical univalence and structured transport | A native univalence construction in the library's cubical model, substitution laws, and transport of state packages including invariants and proofs. See [the native theorem](SquareKit/Internal/Cubical/NativeUnivalence.lean), [checked specializations](Examples/CubicalNativeUnivalence.lean), and [a facade client](Examples/UnivalentAuthorTrial/FacadeOracle.lean). |
| Reactive computation | Denotational FRP, compiled initialized consumers, discrete IO drivers, finite-circuit services, and backend migration with pending work. See [the bounded driver](docs/research/frp-driver.md), [the circuit service](docs/research/indefinite-reactive-service.md), and [in-process peer migration](docs/research/pending-peer-migration.md). |
| External code representations | Graph-core emission with typing/denotation proofs and translation validation; Boolean-circuit lowering to a selected WebAssembly module syntax with invocation proofs. See [graph emission](Examples/GraphEmission.lean) and [Wasm contracts](docs/research/wasm-standard-subset.md). Wasm binary production and external execution remain unfinished. |
| Geometry | Smooth algebra, sheaves, torsors, descent, manifold comparisons, and exact/rational disk-motion realizations. See [manifold clients](Examples/MathlibManifoldRealization.lean), [torsors](Examples/SmoothTorsors.lean), and [numerical motion](docs/research/numerical-motion.md). |
| Probability and interaction | Measurable accept/reject kernels, finite Metropolis–Hastings, sampling, probabilistic progress, and delivery/recovery contracts. See [probability](docs/probability.md), [checked MH compositions](Examples/MetropolisHastings.lean), and [durability](docs/durability-direction.md). |

Textbook work draws on *Algorithm Design with Haskell*, *Verified Functional
Algorithms* (VFA), *Functional Data Structures and Algorithms* (FDSA), and
*Purely Functional Data Structures* (PFDS). See the [ADWH map](docs/research/adwh-reconstruction-map.md)
and [textbook integration](docs/research/textbook-integration.md) for coverage
and remaining work.

## Development environment

Install Nix with `nix-command` and `flakes` enabled, and direnv with its
[shell hook](https://direnv.net/docs/hook.html). From the repository root:

```sh
direnv allow
direnv exec . lake exe cache get
```

The flake supplies the development tools. [lean-toolchain](lean-toolchain) and
the Lake files pin Lean and Mathlib. Initial setup needs network access.
Use `direnv exec . <command>` for noninteractive commands, or enter `nix develop`
for an interactive shell.

The [development guide](docs/development.md#development-environment) covers
toolchain changes and their required checks.

## Build and audit

Run the integrated library check:

```sh
direnv exec . ./check.sh
```

It checks source policy and public-entrypoint coverage, builds the integrated
modules, and runs the exhaustive proof audit. For a focused development build:

```sh
direnv exec . lake build Examples.MappedAggregate
```

A focused build does not replace the integrated check. Validate committed Lean
candidates in the persistent isolated acceptance workspace:

```sh
direnv exec . python3 scripts/check-candidate.py HEAD
direnv exec . python3 scripts/check-candidate.py HEAD --verify
```

This retains private Lake outputs across candidates and runs the full audit each
time. Use `--fresh` for changes to verification inputs or suspected stale outputs,
as defined in the development guide.
Before selecting validation for a change, read the
[full build and audit procedure](docs/development.md#build-and-audit). It defines
candidate requirements, fresh checks, stable inputs, cache-integrity handling,
and tooling regression tests. Documentation-only changes need relevant content
and link checks, not a Lean rebuild.

To run an IO application, follow its own protocol and setup instructions, such
as the [FRP driver](docs/research/frp-driver.md) or
[finite-circuit service](docs/research/indefinite-reactive-service.md).

## Proof and execution boundary

The integrated proof audit allows `propext`, `Classical.choice`, and `Quot.sound`.
It rejects admissions, application-specific axioms, and native-evaluation axiom
shortcuts, including through private declarations. See
[ProofAudit.lean](ProofAudit.lean) and the
[audit details](docs/development.md#proof-audit-details).

A theorem establishes its stated contract under its assumptions. Cost theorems
use explicit execution models and tariffs; they are not wall-clock benchmarks.
Some mathematical constructions are noncomputable. Executable realizations,
external IO, and numerical approximations have separate contracts.

Native univalence concerns paths and equivalences inside the constructed
cubical model; it does not change Lean's equality or kernel. The executable
transport adapter uses supplied executable maps with correctness proofs.
The Wasm result covers a reviewed transcription of selected standard rules;
serialization and execution in an external engine are further boundaries.
The delivered FRP runners are discrete and do not implement general dynamic
switching, an asynchronous scheduler, or crash-recoverable external delivery.

## Library layout

| Location | Contents |
|---|---|
| Root Lean modules | Square/compiler foundations and the aggregate public entrypoint. |
| [SquareKit/](SquareKit/) | Shared structures, interpretations, internal languages, and reusable proofs. |
| [Applications/](Applications/) | Domain implementations with semantic and resource contracts. |
| [Examples/](Examples/) | Checked clients, specializations, compositions, and discriminating cases. |
| [scripts/](scripts/), [ProofAudit.lean](ProofAudit.lean) | Build/audit tooling, executable drivers, and tests. |
| [experiments/](experiments/) | Isolated investigations with their own validation. |
| [docs/research/](docs/research/), [docs/adr/](docs/adr/) | Detailed contracts, investigations, and architecture decisions. |

Use [GLOSSARY.md](GLOSSARY.md) for shared terminology,
[DESIGN.md](DESIGN.md) for architectural entry points, and
[docs/SOURCES.md](docs/SOURCES.md) for references.

## Workstreams and shared components

GitHub Issues hold current task scope, dependencies, and status. These links
locate the main ongoing efforts; shared components often serve several of them.

| Effort | Scope and coordination |
|---|---|
| Repository tooling | [End-to-end native tooling #591](https://github.com/VladimirMarko/conaled/issues/591), [verification refinement #43](https://github.com/VladimirMarko/conaled/issues/43), and [verified artifact reuse #222](https://github.com/VladimirMarko/conaled/issues/222). |
| Categorical compilation | [Felix port and completion #8](https://github.com/VladimirMarko/conaled/issues/8). |
| Internal languages and transport | [Shared language #36](https://github.com/VladimirMarko/conaled/issues/36), [preservation interfaces #235](https://github.com/VladimirMarko/conaled/issues/235), [dependent semantics #289](https://github.com/VladimirMarko/conaled/issues/289), and [reusable theories #290](https://github.com/VladimirMarko/conaled/issues/290). |
| Construction and observation | [Research direction](docs/research/construction-observation-research-assessment.md), [theory extensions #288](https://github.com/VladimirMarko/conaled/issues/288), and [logical correspondences #200](https://github.com/VladimirMarko/conaled/issues/200). |
| Reactive systems and durability | [FRP runtime #27](https://github.com/VladimirMarko/conaled/issues/27), [durability #225](https://github.com/VladimirMarko/conaled/issues/225), and [runtime contracts](docs/research/frp-runtime-follow-up.md). |
| Algorithms and textbook integration | [ADWH #149](https://github.com/VladimirMarko/conaled/issues/149), [textbooks #558](https://github.com/VladimirMarko/conaled/issues/558), and [data-structure toolkits #174](https://github.com/VladimirMarko/conaled/issues/174). |
| Geometry | [Orbifold theory #32](https://github.com/VladimirMarko/conaled/issues/32) and [simulator #34](https://github.com/VladimirMarko/conaled/issues/34). |
| Hardware realizations | [FPGA and hardware architecture directions](docs/extensions.md#hardware-research-and-external-realizations). |

Choose module and interface boundaries from actual reuse and dependencies.
Workstream names are coordination aids; useful work need not wait for a new
classification or umbrella issue. Link the issue that owns a deliverable's
acceptance criteria, and update this index when it stops helping readers find work.

## Parallel and experimental developments

Alternative implementations can coexist when their contracts and purpose are
clear. Integrated experimental code meets the same proof and validation standard
as the rest of the library; label its evolving interface and unresolved questions
in its module or application documentation. Isolated experiments need their own
validation and are outside the main build.

Use checked specializations alongside formal claims and review statements
against their intended mathematics. [AGENTS.md](AGENTS.md) gives the repository's
implementation and independent-review workflow. Evaluate changes by mathematical
quality, usability, and maintainability; development history helps explain
constraints and migration choices.

## Historical material

[docs/history/](docs/history/) holds source material useful for recovery and
understanding design choices. For current APIs, start with the code and examples
above. Historical checkpoints are outside the integrated build.
