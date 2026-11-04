# conaled

A Lean monorepo for compositional verified programs and mathematics, extending
Conal Elliott's work on categorical compilation. It develops reusable
operations, semantic contracts, and proofs, with checked applications in
compilation, internal languages, geometry, reactive computation, and algorithm
design. Felix is a mathematical and architectural reference, not a build
dependency.

The long-term ambition is to **make the mathematical setting a first-class
parameter of programming and proof**: express what a construction needs, then
reuse it in settings that supply those operations and principles. The
[language direction](docs/language-direction.md) explains this goal and its
design tests. Current developments implement particular fragments and
interpretations; they do not yet supply a universal language for transporting
arbitrary Lean proofs.

## Finding your way

- [SquareApplications.lean](SquareApplications.lean) is the public entrypoint
  for the integrated library. Its imports lead to checked examples and domain
  implementations.
- [Workstreams and shared components](#workstreams-and-shared-components) links
  ongoing efforts to their scope-owning issues. GitHub Issues hold acceptance
  criteria, dependencies, and current task status.
- [APPLICATIONS.md](APPLICATIONS.md) explains the original compiler application
  families and their compositions. It is not a complete inventory of the newer
  internal-language, geometric, and algorithm developments.
- [GLOSSARY.md](GLOSSARY.md), the [architectural standard](docs/agents/architectural-quality.md),
  and [ADRs](docs/adr/README.md) record shared terminology and design constraints.
- [Source provenance](docs/SOURCES.md) and [research notes](docs/research/)
  connect developments to their references, assessments, and remaining questions.

## What is in the library

These are entry points into integrated code, not claims that the surrounding
research programs are complete. Each theorem's assumptions and preservation
contract determine its scope.

| Area | Implemented material and entry points |
|---|---|
| Categorical compilation | Exact and relational squares, structure-preserving maps, law transport, and typed compilers. Start with [Compiler.lean](Compiler.lean), [FirstOrder.lean](FirstOrder.lean), and the [Felix implementation record](docs/research/felix-parity-implementation.md). |
| Compiler applications | Analytic AD, polynomial derivative towers, scan and FFT, stack code, matrices, incremental updates, interval enclosures, language derivatives and parsers, and circuit timing. See [APPLICATIONS.md](APPLICATIONS.md). |
| Internal languages and models | Graph and logical reasoning, dependent fragments, sheaf and presheaf interpretations, groupoid transport, higher-identity examples, and classifiers. Start with [SquareKit/Internal/](SquareKit/Internal/), [dependent-source examples](Examples/DependentSource.lean), and [Sierpiński examples](Examples/SierpinskiSheaf.lean). |
| Emission and interpretation | A bounded graph-core emitter with typing and denotation proofs, translation validation, and checked Lean callers. See the [implementation record](docs/research/graph-emission-implementation.md) and [caller examples](Examples/GraphEmission.lean). |
| Smooth and orbifold geometry | Smooth algebra and sheaf constructions, descent and torsors, manifold comparisons, frame transport, and exact and rational disk-motion realizations. See [manifold examples](Examples/MathlibManifoldRealization.lean), [torsor examples](Examples/SmoothTorsors.lean), and [numerical motion](docs/research/numerical-motion.md). |
| Functional reactive programming | Denotational events/switching, frontier protocols, an executable command engine, compiled initialized reactive consumers and sequential request lifecycles. See the [lifecycle](docs/research/request-lifecycle.md), [finite-circuit indefinite service](docs/research/indefinite-reactive-service.md), and [current limits and follow-up](docs/research/frp-runtime-follow-up.md). |
| Probability and Monte Carlo | Measurable accept/reject kernels, exact finite Metropolis–Hastings, compositional interpretation, and probabilistic finite delivery. See [probability contracts](docs/probability.md), [stochastic progress](docs/probabilistic-progress.md), and [checked MH compositions](Examples/MetropolisHastings.lean). |
| Algorithm derivation and data structures | Reconstructed sorting, selection, graph, search, dynamic-programming, and sequence developments, with refinement and explicit resource results. The [ADWH reconstruction map](docs/research/adwh-reconstruction-map.md) records provenance and remaining scope; [resource examples](Examples/Resources.lean) exercise composition and reweighting. |

For examples of composition, [ArithmeticPipeline](Examples/ArithmeticPipeline.lean)
connects incremental updates, stack recomputation, and interval enclosure;
[JetScan](Examples/JetScan.lean) connects polynomial derivative coefficients to
scan-based evaluation; and [Resources](Examples/Resources.lean) connects
sequential algorithm executions to resource accounting. These examples are
checked claims with explicit contracts, alongside concrete specializations.

## Library layout

| Location | Role |
|---|---|
| Root Lean modules | Original square and compiler foundations, the public entrypoint, and verification. `Dependent.lean` is the original shallow family model; newer dependent developments live under `SquareKit/`. |
| [SquareKit/](SquareKit/) | Shared mathematical structures, interpretations, internal-language machinery, and reusable proofs. |
| [Applications/](Applications/) | Domain mathematics, implementations, and semantic proofs. These directories are not a list of runnable products. |
| [Examples/](Examples/) | Checked specializations, cross-component compositions, and executable examples. |
| [ProofAudit.lean](ProofAudit.lean), [scripts/](scripts/) | Integrated-library proof auditing and build/check tooling. |
| [experiments/](experiments/) | Isolated investigations and preserved checkpoints with their own scope and validation records. Presence here does not establish integration or acceptance. |
| [docs/research/](docs/research/), [docs/adr/](docs/adr/), [docs/history/](docs/history/) | Research evidence, architectural decisions, and preserved historical sources. |

The [glossary](GLOSSARY.md) distinguishes development efforts, reusable domain
libraries, mathematical applications, and runnable software applications.
A workstream can cross several directories and produce several systems.
[ADR 0001](docs/adr/0001-modules-and-proof-dependencies.md) governs the existing
layout; any migration must keep imports, Lake targets, public coverage, and the
proof audit consistent.

## Workstreams and shared components

This is a navigational index of overlapping efforts. Use it to find related
work and the issues that own scope and acceptance criteria. It is neither an
exhaustive inventory nor a fixed hierarchy; nested efforts live in their
umbrella issues. Research notes provide context, while GitHub Issues own task
scope, dependencies, and completion status.

| Effort | Scope | Issues and context |
|---|---|---|
| Felix port and completion | Port and extend Felix's constructions and proofs beyond the initial parity milestone | [#8](https://github.com/VladimirMarko/conaled/issues/8), [implementation evidence](docs/research/felix-parity-implementation.md) |
| Shared internal language | Reusable internal reasoning, interpretations, and differential cohesive models | [#36](https://github.com/VladimirMarko/conaled/issues/36), [language direction](docs/language-direction.md), [nested efforts](docs/research/language-architecture-research.md#approved-follow-up-work) |
| Construction and observation | Compatible construction, observation, interpretation and extension; duality and verified presentations | [Agenda](docs/research/duality-language-directions.md), [ordinary composition](docs/research/compositional-constructor-observer-laws.md), [indexed composition](docs/research/indexed-constructor-observer-laws.md), [full finite parser composition #274](https://github.com/VladimirMarko/conaled/issues/274), [bialgebraic assessment and follow-ups](docs/research/bialgebraic-semantics-adoption.md), [relation to the research agenda](docs/research/construction-observation-research-assessment.md); coordinated with #36/#200/#235/#8 |
| Logical correspondences and transport | Prioritize demonstrated preservation-law reuse while continuing logic classification and interpretation research | [#200](https://github.com/VladimirMarko/conaled/issues/200), [classification](https://github.com/VladimirMarko/conaled/issues/201), [preservation architecture #235](https://github.com/VladimirMarko/conaled/issues/235), [external discovery assessment](docs/research/external-discovery-assessment.md) (#280; follow-ups #286/#287), [architecture and author trials](docs/research/preservation-architecture.md), [first experiment #231](https://github.com/VladimirMarko/conaled/issues/231), [implemented-contract inventory](docs/research/preservation-contract-inventory.md) |
| Compositional theory extensions | Model expansion, admissibility and retained witnesses | [#288](https://github.com/VladimirMarko/conaled/issues/288), [initial experiment #291](https://github.com/VladimirMarko/conaled/issues/291), [research agenda](docs/research/language-research-agenda.md) |
| Dependent semantics and coherence | Reusable substitution structure and explicit context/identity laws | [#289](https://github.com/VladimirMarko/conaled/issues/289), [local-universes comparison #292](https://github.com/VladimirMarko/conaled/issues/292) |
| Reusable theories and proof transport | Discover, publish and interpret mathematical requirements | [#290](https://github.com/VladimirMarko/conaled/issues/290), [author trial #293](https://github.com/VladimirMarko/conaled/issues/293), [theory networks #294](https://github.com/VladimirMarko/conaled/issues/294) |
| Temporal logic and FRP | Constructive temporal programs, monitoring, and comparisons with existing FRP observations and progress guarantees | [#204](https://github.com/VladimirMarko/conaled/issues/204), a focused sub-workstream of [#200](https://github.com/VladimirMarko/conaled/issues/200), coordinated with [#27](https://github.com/VladimirMarko/conaled/issues/27) and [#31](https://github.com/VladimirMarko/conaled/issues/31) |
| Modular abstraction and cost transport | Assess Harper's methods and reuse client proofs and cost bounds across representations | [#208](https://github.com/VladimirMarko/conaled/issues/208), a focused sub-workstream of [#200](https://github.com/VladimirMarko/conaled/issues/200), coordinated with [#174](https://github.com/VladimirMarko/conaled/issues/174) and [#177](https://github.com/VladimirMarko/conaled/issues/177) |
| FRP | Reactive semantics, compiled discrete execution, long-running state and external driver contracts | Runtime scope [#27](https://github.com/VladimirMarko/conaled/issues/27), indefinite-service class [#234](https://github.com/VladimirMarko/conaled/issues/234), request protocol/retention [#232](https://github.com/VladimirMarko/conaled/issues/232), bounded driver [#233](https://github.com/VladimirMarko/conaled/issues/233), [evidence and sequence](docs/research/frp-runtime-follow-up.md) |
| Compositional durability | Program-specific persistence, recovery, observation and coordination contracts with verified realizations | [#225](https://github.com/VladimirMarko/conaled/issues/225), coordinated with [#196](https://github.com/VladimirMarko/conaled/issues/196); [direction](docs/durability-direction.md), [recovery assessment](docs/research/durability-contract-experiment.md), [storage and diagnostic comparison](docs/research/persistence-diagnostic-specialization.md), implementation follow-ups [#240](https://github.com/VladimirMarko/conaled/issues/240) and [#241](https://github.com/VladimirMarko/conaled/issues/241) |
| Orbifolds | Geometric foundations, realizations, and simulator development | Theory [#32](https://github.com/VladimirMarko/conaled/issues/32), simulator [#34](https://github.com/VladimirMarko/conaled/issues/34), [research](docs/research/orbifold-geometry.md) |
| Algorithm Design with Haskell reconstruction | Textbook algorithms and proofs, derivation, optimization, and certified evaluation | [#149](https://github.com/VladimirMarko/conaled/issues/149); placement as a distinct workstream or within existing efforts remains open |
| Data-structure toolkits | Specification-preserving representation choices relative to target capabilities and workloads | [#174](https://github.com/VladimirMarko/conaled/issues/174), [target capabilities](docs/research/data-structure-target-capabilities.md), [resource contracts](docs/research/data-structure-resource-contracts.md); bounded implementation [#239](https://github.com/VladimirMarko/conaled/issues/239) follows [#185](https://github.com/VladimirMarko/conaled/issues/185) |
| FPGA development | Executable hardware experiments and external tool interfaces | [Research agenda](docs/extensions.md#hardware-research-and-external-realizations); proposed scope |
| Hardware architecture derivation | Derive and compare realizations under different architectural choices | [Research agenda](docs/extensions.md#hardware-research-and-external-realizations); proposed scope |

Keep this structure provisional. Add, split, combine, rename, or retire entries
when that helps people find work or resolve coordination problems. A task may
contribute to several efforts, and useful work need not wait for a workstream
classification. Clarify which issue owns a deliverable's acceptance criteria
and link its consumers instead of duplicating the task. Update the index when
its links or descriptions misdirect readers; do not require exhaustive
classification or a new umbrella issue merely to fill a row.

Workstream names must not calcify the project's architecture. Choose module,
package, and executable boundaries from actual reuse, dependencies, build
needs, and runnable systems. Allow research to change the organization;
revisit applicable ADRs when implementation boundaries change.

Shared components and standards cut across these efforts: categorical
foundations, compiler frontends and backends ([library layout](#library-layout)),
the [architectural quality standard](docs/agents/architectural-quality.md), and
the [Mathlib dependency policy](docs/adr/0001-modules-and-proof-dependencies.md).
The shared categorical foundation supports more than the current compiler
frontends.

The [scope assessment](docs/research/development-scope.md) distinguishes existing
Felix investigation and hardware proofs from the remaining research.

## Development environment

Install Nix with `nix-command` and `flakes` enabled, and install direnv with
its [shell hook](https://direnv.net/docs/hook.html) enabled. From the repository
root, run `direnv allow`. The checked-in `.envrc` loads the flake shell whenever
you enter the directory. Without shell integration, use `nix develop`.

`flake.nix` declares the supporting tools, and `flake.lock` pins their Nixpkgs
revision. The shell provides elan, Python, Git, curl, direnv, and ripgrep.
Elan selects and downloads Lean (including Lake) from `lean-toolchain` on first
use; Lake resolves library revisions from `lake-manifest.json`. Initial setup
and cache downloads require network access.

For agent commands without an interactive shell, use `direnv exec . <command>`
after allowing the directory, or `nix develop --command <command>`.
Add additional project tools to the shell's `packages` list. Tools from the
existing Nixpkgs input share its lock; update that pin intentionally with
`nix flake update nixpkgs`. Check in `flake.nix` and `flake.lock` together.
Validate tooling changes with `nix flake check` and, for example,
`nix develop --command lean --version`.

## Build and audit

Lean is pinned in [lean-toolchain](lean-toolchain), the Mathlib requirement in
[lakefile.toml](lakefile.toml), and resolved dependency revisions in
[lake-manifest.json](lake-manifest.json). Inside the development shell:

```sh
lake exe cache get
./check.sh
```

The first command obtains the pinned dependencies and their compiled cache.
`./check.sh` is the routine acceptance command. It checks the source policy and
public-entrypoint coverage, builds every integrated module with stock Lake's
incremental dependency tracking, then executes `ProofAudit.lean`. The exhaustive
audit runs on every invocation, including when compilation is entirely cached.
Successful builds remain in Lake's normal output directories for later reuse.
Lake owns incremental scheduling; this wrapper adds no persistent cache. Before
and after the incremental build, an output-integrity guard compares project
artifacts with the output hashes in their saved Lake traces. Missing or
inconsistent evidence causes invalidation before the build; a mismatch after
the build fails verification before the audit. Guarded builds disable Lake
artifact-cache restoration/writes and rehash inputs, while reusing existing
dependency build outputs. The guard uses the pinned Lake hash implementation.

For acceptance of a committed candidate in its isolated checkout:

```sh
./check.sh --candidate HEAD
./check.sh --verify-candidate HEAD
```

The first command requires a clean Git checkout, including the index and
nonignored untracked files, and requires all integrated Lean sources to be
tracked. Dependency checkouts must be clean and match the Git revisions in
`lake-manifest.json`. It checks these conditions before compilation and again
after the audit, then atomically writes `.lake/verification.json` with the
resolved commit, dependency revisions, compiler version, mode, and completion
time. Combine `--candidate HEAD` with `--fresh` when fresh validation is needed.

`--verify-candidate` checks that the success record still matches the current
candidate, dependencies, and compiler without compiling or rerunning the audit.
Use it immediately before accepting the recorded candidate. It uses the mode
in the record; omit `--fresh` and `--jobs`. Starting any new validation removes
the previous record, and only successful candidate validation writes a new one.
Ordinary `./check.sh` remains available for uncommitted development work and
does not produce a candidate success record. Other required tests and reviews
need their own evidence; this record covers only this verification command.

This is bookkeeping for trusted local checkouts, not a certificate of artifact
integrity or an immutable input snapshot. Before/after checks cannot detect
changes made and restored during the run, ignored external inputs, or hostile
Git metadata. Keep the isolated checkout stable throughout validation and
acceptance. Candidate records currently support Git-pinned Lake dependencies.

For focused development, use `lake build Applications.Interaction.Measurement`
(or another module target). A bare `lake build` builds the configured library
and audit, but does not replace `./check.sh`'s source-policy and coverage checks.

Use `./check.sh --fresh` for a cache-independent project rebuild after changing
the build tooling, toolchain, or dependency configuration, or when stale outputs
are suspected. The [fresh verification workflow](.github/workflows/fresh-verification.yml)
also runs weekly on the default branch and supports manual dispatch once pushed
to GitHub with Actions enabled. Fresh mode recompiles every project module into
a private temporary directory, audits those outputs, and removes the directory.
It reuses external dependency caches but neither reuses project artifacts nor
populates Lake's incremental cache. Use `--fresh --jobs 1` for serial compilation,
or `--fresh --jobs N` to set a memory-appropriate limit (default: up to four).

Both modes discard caller `LEAN_PATH` and verify the compiler version against
`lean-toolchain`. Incremental mode uses Lake's configured import paths and
compiler. Fresh mode uses only its new project outputs and dependency caches;
it also supports `LEAN=/absolute/path/to/lean`. `--jobs` and `LEAN` overrides are
rejected outside fresh mode rather than silently ignored.

Keep sources, dependencies, and configuration stable during a check. Use an
isolated checkout when other agents may edit them, and do not share writable
project build directories across active checkouts. Routine acceptance trusts
Lake's input tracking and local artifacts; it is not a certificate against
artifact tampering or undeclared external inputs. Periodic fresh builds provide
an independent check of project cache state. Future verified reuse is tracked
in [#222](https://github.com/VladimirMarko/conaled/issues/222).

The local output-integrity guard is a temporary mitigation for mixed project
artifacts, not the verified-reuse contract in #222. Agreement with a trace does
not prove that artifacts were compiled from the claimed inputs. Lake's hashes
are noncryptographic; this is not authentication against hostile substitution.
The guard does not prevent changes between checking and consumption or establish
external dependency-cache integrity. Direct `lake build` invocations and editor
consumers bypass it. Keep the stable-checkout discipline, exhaustive audit, and
periodic fresh verification; see the
[mitigation scope and limitations](docs/research/lake-output-cache-mismatch.md#local-mitigation).

The guard supports the repository's standard TOML build layout and pinned trace
schema. Custom project build/source directories, a `lakefile.lean`, or explicitly
enabling the project's artifact cache are rejected. Unknown trace evidence
triggers rebuilding; if a new build still produces unsupported evidence,
verification fails. Toolchain or layout changes must update and test the adapter.

For guard diagnostics, automatic recovery, and failures requiring investigation,
follow the [Lake integrity incident runbook](docs/agents/lake-integrity-incidents.md).
While the temporary tracker is open, record unexpected incidents in [#272](https://github.com/VladimirMarko/conaled/issues/272);
normal cold-build invalidations need no report. The tracker defines how to alert
the owner when an already investigated failure recurs, including sub-agent relay.

Both modes cover root Lean modules and `SquareKit/`, `Applications/`, and
`Examples/`; archived sources and isolated `experiments/` require their own
validation. Generated `.olean`, `.ilean`, `.lake`, and cache files are not source
artifacts. The command reports build, audit, and total elapsed times.

After `lake build`, run `lake env python3 scripts/test-proof-audit.py` to check
that the audit rejects private forbidden dependencies, admissions, and unsafe
source declarations. Its temporary fixtures also check that an unused external
axiom does not cause a false rejection. Two additional suites need only the
development shell and cached dependencies:

```sh
python3 scripts/test-check.py
python3 scripts/test-proof-audit-roots.py
```

The first exercises incremental reuse and invalidation, repeated auditing, fresh
compilation, concurrency, ordering, stale artifacts, coverage, and failure exits
through `check.sh`. The second compares the audit's
exact root set with an independent exhaustive environment scan, including
private, generated, and current-module declarations. For diagnostics,
`set_option trace.ProofAudit.roots true in #audit_project_axioms` prints the
logical roots. The normal audit uses project module metadata to avoid scanning
unrelated dependency declarations, and Lean's cached transitive axiom summaries.
Formal refinement proofs for these checks are tracked separately in
[#43](https://github.com/VladimirMarko/conaled/issues/43).

The original dependency-free foundation remains available:

```sh
./check-foundation.sh
```

It checks the six original root modules using Lean alone. That smaller command
does not validate the rest of the monorepo.

## Proof and execution boundary

The full check ends with a transitive axiom audit of integrated local kernel
declarations, including private definitions and generated proof auxiliaries.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Admissions, application-specific axioms, and native-evaluation axiom shortcuts
are rejected. See [ProofAudit.lean](ProofAudit.lean) for the precise treatment
of logical declarations and compiler-generated runtime declarations.

A checked theorem establishes its stated mathematical contract. It does not
by itself establish a runtime, compiler, or physical-system performance claim.
Some analytic specifications are noncomputable; executable realizations and
approximation results have their own domains and error assumptions. Resource
and cost theorems depend on explicit models and workloads. Their conclusions
do not automatically describe Lean allocation or wall-clock performance.

The dependent-language and emission developments cover specified fragments.
The FRP protocols do not constitute a complete scheduler or runtime, and the
geometric developments do not establish delivery of a complete simulator.
Consult the linked examples, research records, and scope-owning issues for
what each development supplies and what remains open.

## Parallel and experimental developments

`master` supports multiple implementations and parallel lines of development.
An implementation can be merged while its broader research question remains
open, provided its stated scope is coherent and it meets the repository's
architecture, checked-example, build, and proof-audit requirements. Alternative
implementations can coexist in distinct modules and namespaces, reuse shared
abstractions, and state their own semantic contracts. Merging one does not
select it as the sole implementation or require replacing another.

Mark an experimental implementation in its module documentation and link its
scope and unresolved questions from the relevant research or application note.
Experimental status means the design and interface may evolve. Integrated
experimental code has the same proof standard as the rest of the library.
Isolated experiments and historical imports need their own validation records;
the main build does not certify them.

For formal development, use checked specializations and applications alongside
the theory, and review each new or changed statement against its intended
mathematics. [AGENTS.md](AGENTS.md#implementation-and-validation) routes
implementation tasks to the default independent review workflow and validation
requirements. Optional originator review adds retained-intent assessment within
the same [review procedure](docs/agents/review-loop.md#reuse-across-review-entry-points).

## Historical material

The [square-compiler archive](docs/history/square-compiler/README.md) preserves
the original `foundation-v1` design, historical verification output, and its
checksum manifest. These records describe earlier checkouts; use the
[current design pointers](DESIGN.md) and [build/audit instructions](#build-and-audit)
for today's work. [APPLICATIONS.md](APPLICATIONS.md) remains a maintained,
selective coverage document, including later developments; it is not part of
the frozen archive.
[docs/history/](docs/history/) preserves imported discussions and source material;
use its provenance and scope notes before treating those artifacts as current
implementation evidence.
