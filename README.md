# Compiling with commutative squares: applications and extensions

A Lean reconstruction of Conal Elliott's categorical compilation program,
extended with analytic automatic differentiation, higher-order functions,
all-order polynomial derivatives, generic scan and FFT, stack compilation,
linear matrices, finite incremental updates, interval analysis, convolution,
language derivatives and parsing, and stable-signal circuit timing.

The project is an independent development using Felix's general style of
representations, compositional semantic contracts, and commuting squares.
Felix is a mathematical reference, not a build dependency. The public entrypoint
is `SquareApplications.lean`.

**Our language-design ambition is to make the mathematical setting a first-class
parameter of programming and proof.** Authors should be able to factor out the
structure and principles an argument needs, then reuse familiar reasoning in
every setting that supplies them. Categorical compilation and internal-language
development should progressively constrain this language's shape. Read the
[shared language direction](docs/language-direction.md) for the goal, design
criteria and distinction from current capabilities.

**Every implemented correctness claim has a Lean proof.** The complete build
ends with an exhaustive transitive axiom audit of local kernel declarations,
including private definitions and generated proof auxiliaries. No placeholder,
application-specific axiom, or unchecked termination assumption is admitted.

Start with [APPLICATIONS.md](APPLICATIONS.md) for the results, cross-application
compositions, and exact coverage. The [historical foundation design](DESIGN.md)
is preserved unchanged from `foundation-v1`; its build and coverage statements
describe that earlier delivery, not the current application extension.

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
Experimental status means the design and interface may evolve. Its proved
claims retain their stated assumptions and the same proof standard as the rest
of the library. A radical architectural departure may need isolated exploration;
experimental status alone is not a reason to keep checked work off `master`.

The [FRP frontier protocol](docs/research/frp-runtime-scope.md) is an experimental
implementation of complete-window source updates and merge observations. Its
scope does not include a scheduler or a complete FRP runtime.

The [rational disk motion backend](docs/research/numerical-motion.md) is an
experimental executable realization of timed move, turn, and hold commands.
It proves bounded coordinate error for position and frame, checks its valid
domain, and preserves quarter-turn representative changes.

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

The application libraries use **Lean 4.35.0** and **Mathlib v4.35.0**, pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679` by the checked-in manifest. Inside
the development shell:

```sh
lake exe cache get
./check.sh
```

The first command obtains the pinned dependencies and their compiled cache.
`check.sh` uses Python's standard library, resolves the local import graph,
rejects source modules omitted from the public entrypoint, and **rechecks every
project module from source** before running `ProofAudit.lean`. Independent
modules compile concurrently after their local imports succeed. The default
is up to four workers; use `./check.sh --jobs 1` for serial checking or
`--jobs N` to set another memory-appropriate limit. The command reports
compilation, audit, and total elapsed times.

Each full check uses a private temporary output directory under `.lake`, removed
when the check finishes. It reuses external dependency caches but does not reuse
project artifacts or populate Lake's incremental build cache. Source-adjacent
`.olean` files and existing Lake project outputs cannot shadow the fresh outputs.
The command replaces caller `LEAN_PATH` with the fresh output directory and
cached dependency paths. It accepts `LEAN=/absolute/path/to/lean` and verifies
its version against `lean-toolchain`. Keep sources and dependencies stable during
a check. Historical delivered verification output is in
[verification.txt](verification.txt).

For incremental development, `lake build` builds the same modules and audit.
Generated `.olean`, `.ilean`, `.lake`, and cache files are not source artifacts.
They are intentionally omitted from the download.

After `lake build`, run `lake env python3 scripts/test-proof-audit.py` to check
that the audit rejects private forbidden dependencies, admissions, and unsafe
source declarations. Its temporary fixtures also check that an unused external
axiom does not cause a false rejection. Two additional suites need only the
development shell and cached dependencies:

```sh
python3 scripts/test-check.py
python3 scripts/test-proof-audit-roots.py
```

The first exercises fresh compilation, concurrency, ordering, stale artifacts,
coverage, and failure exits through `check.sh`. The second compares the audit's
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
does not validate the application extension.

## Library layout

The [shared glossary](GLOSSARY.md) distinguishes **workstreams** (development
efforts), **domain libraries** (reusable mathematics and implementations),
**mathematical applications** (uses of constructions and theorems), and
**software applications** (runnable systems). A workstream can span several
libraries; a simulator can use several mathematical applications.

`Applications/` is the existing home for domain implementations and their
semantic proofs, as specified by [ADR 0001](docs/adr/0001-modules-and-proof-dependencies.md).
It is neither a list of runnable programs nor a complete map of workstreams.
Its contents include specializations, domain theory, and compiler backends.

| Location | Purpose |
|---|---|
| `Squares.lean`, `Compiler.lean`, `SquareCompiler.lean` | Exact representation squares, products/exponentials, intrinsically typed simply typed source, target-parametric compilation, and semantic correctness. |
| `FirstOrder.lean` | Cartesian source compilation for targets that do not support arbitrary function types. |
| `Dependent.lean` | Original shallow split-family model and dependent substitution, context extension, Π/Σ certificates. |
| `SquareKit/` | Relational squares, witness squares, synchronized representations, full-STLC and first-order relational compiler instances, shared arithmetic syntax. |
| `Applications/AD/` | Actual Fréchet derivatives; forward, reverse, continuation and adjoint modes; direct generalized compilation; higher-order curve relation; all-order polynomial towers. |
| `Applications/Parallel/` | Statically shaped data, compositional scan recipes, scan-based polynomial evaluation, recursive Cooley–Tukey FFT, exact complex semantics and finite-field executions. |
| `Applications/Stack/` | Typed instruction sequences, stack execution, and source correctness preserving every stack tail. |
| `Applications/Linear/` | Matrices over commutative semirings; coordinate laws and a source compiler that emits actual matrices. |
| `Applications/Incremental/` | Finite changes and cache invariants, with a shared arithmetic source instance. |
| `Applications/Intervals/` | Exact rational enclosures, four-corner multiplication, and higher-order source compilation by logical relations. |
| `Applications/Convolution/` | Word-indexed weighted series, semiring laws, sparse polynomial normalization, coefficient and support homomorphisms. |
| `Applications/FRP/` | Historical FRP specifications repaired and checked: chronological events and time-indexed batches, carrier equivalences, finite histories, and strict switching. [Integration and checked bridges](docs/frp-integration.md); [provenance](docs/history/frp/README.md). |
| `Applications/Languages/` | Optimized derivatives, recognizers, finite trie observations, proof-relevant language isomorphisms, a total witness parser, and cross-representation proofs. |
| `Applications/Timing/`, `Applications/Circuits/` | Setup/hold interval semiring, stable signals, independent values and linear timing, matrices, typed circuit AST, compiled adders and a proved carry hazard. |
| `Examples/` | Universal compositions between independently implemented backends, plus executable displays. |
| `ProofAudit.lean` | Exhaustive dependency traversal; rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`. |
| `docs/adr/` | Ten architecture decision records, with motivations, rejected alternatives, evidence, and limits. |

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
| FRP | Reactive semantics, representations, and runtime research | [Integration record](docs/frp-integration.md), runtime scope [#27](https://github.com/VladimirMarko/conaled/issues/27), incremental state machine [#31](https://github.com/VladimirMarko/conaled/issues/31) |
| Orbifolds | Geometric foundations, realizations, and simulator development | Theory [#32](https://github.com/VladimirMarko/conaled/issues/32), simulator [#34](https://github.com/VladimirMarko/conaled/issues/34), [research](docs/research/orbifold-geometry.md) |
| Algorithm Design with Haskell reconstruction | Textbook algorithms and proofs, derivation, optimization, and certified evaluation | [#149](https://github.com/VladimirMarko/conaled/issues/149); placement as a distinct workstream or within existing efforts remains open |
| Data-structure toolkits | Reusable construction, assessment, and optimization across settings | [#174](https://github.com/VladimirMarko/conaled/issues/174), [research](docs/research/functional-data-structures.md) |
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

The current source layout remains in place. A possible cleanup would separate
shared foundations, compiler machinery, domain libraries, and executable
systems, while workstream documents link across those components. This needs
a migration design against ADR 0001: import paths, public entrypoints, Lake
targets, source coverage, and the proof audit must agree on any new layout.
Creating a directory or Lake package for each workstream would obscure shared
dependencies. Separate packages should follow actual dependency or build
boundaries; separate executable targets should follow runnable systems.

## Composability tests

These are theorems about all relevant programs and inputs:

* `Examples.ArithmeticPipeline.stack_after_update`: stack recomputation equals
  the separately compiled incremental update, including arbitrary stack tails.
* `Examples.ArithmeticPipeline.incremental_output_enclosed`: the separately
  compiled interval result encloses that updated output.
* `Examples.MatrixStack.jointSquare`: synchronize actual matrix and bytecode
  implementations for every term of their common linear source language.
* `Examples.JetScan.source_jet_scan`: compile any polynomial expression's
  derivative of any order, package its coefficients in a type indexed by a
  scan plan, and evaluate it using the scan implementation.
* `LanguageDerivatives.normalized_product_snapshot`: normalize sparse weighted
  convolution, forget weights, compile to regex, and observe a trie, with one
  theorem relating the result to the original coefficient.
* `LanguageDerivatives.recognizers_agree`: independent optimized Boolean and
  proof-relevant parsers agree for every regex and input word.
* `Applications.Circuits.Circuit.compile_matrix_stable`: a source circuit's
  matrix-calculated output intervals satisfy its signal-stability contract.

## Git history

The archive includes `CompilingWithSquares.bundle`, containing `main` and the
tags `foundation-v1` and `applications-v2`. To obtain a normal working repository:

```sh
git clone CompilingWithSquares.bundle CompilingWithSquares-history
cd CompilingWithSquares-history
git log --reverse --oneline
git diff foundation-v1..applications-v2 --stat
```

The history records implementation/integration order: preserved foundation;
shared architecture; stack; parallel algorithms; incremental; intervals;
languages; AD; higher-order relations; linear matrices; composition; timing;
complete build/audit and documentation. Publication chronology is documented
separately in [docs/SOURCES.md](docs/SOURCES.md).

## Proof and execution boundary

The foundational axiom whitelist is explicit; this is not an assertion of an
axiom-free logic. Generic interfaces have local proof fields, and all supplied
primitive instances discharge those fields. Source-to-backend correctness
is relative to the explicitly defined primitive meanings.

Real/complex analytic specifications and some polynomial preparation operations
are noncomputable Lean mathematics. Rational arithmetic, finite syntax,
instruction execution, finite-field FFT examples, and the provided parsers
have executable implementations. There is no claim of certified floating-point
rounding, allocation cost, scheduling cost, netlist optimization, or physical
hardware implementation.

The higher-order AD theorem is a curve logical relation, with fixed sum tags
along a curve. The higher-derivative tower compiler is complete for polynomial
expressions. The FFT factor grammar has leaves of size one or two and arbitrary
composition trees. Language convolution uses finite words and finite splits.
The dependent model remains shallow: this extension does not introduce a full
dependent-language frontend or formalize the LCCC/type-theory correspondence.

See the individual ADRs and [APPLICATIONS.md](APPLICATIONS.md) for precise
restrictions and the unimplemented parts of the original papers.
