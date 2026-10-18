# Evidence for development scope and terminology

This note distinguishes existing investigations and implementations from planned
work. It reviews local sources for repository organization; it adds no upstream
capability claims and reports no new Lean or Agda build.

## Felix investigation and parity

Felix has already received a source-based investigation. The
[parity inventory](felix-parity.md#evidence-and-scope) records the inspected
upstream revision, principal import surface, additional modules, and proof-body
inspection limits. Its capability tables cover categorical operations, laws,
maps, law transport, comma constructions, relations, source integration, and
broader constructions deferred from the initial milestone. Thus a fresh effort
should begin by auditing and extending that inventory, rather than assuming no
upstream investigation exists.

The [implementation report](felix-parity-implementation.md#p1p6-coverage) maps the
initial milestone to local declarations and consumers. Its recorded build and
review revisions delimit its evidence; historical “missing” entries in the
earlier inventory describe the inspected baseline, not the current tree.

Three scopes need separate names:

| Scope | Existing evidence and boundary |
|---|---|
| Architectural parity milestone | The [ordered plan](felix-parity-plan.md) specifies P1–P6 and their acceptance criteria; the implementation report records their delivery evidence. |
| Full Felix port and completion | [Architectural guidance](../agents/architectural-quality.md#scope-of-parity) assigns this broader objective to issue #8. The initial inventory includes deferred capabilities, but does not establish a complete port or completion of upstream TODOs. |
| Architectural quality standard | The same [guidance](../agents/architectural-quality.md) requires reusable operations, semantic equivalence, laws, maps, and checked specializations when designing abstractions. This applies across developments and persists beyond a milestone. |

A complete upstream coverage assessment should account for the chosen revision's
entire source surface, map each relevant construction to local coverage or an
explicit exclusion, and distinguish definitions, proved laws, and unfinished
work. The existing report supplies a starting inventory and selected local
implementation evidence, not evidence that this broader objective is complete.

## Circuits, FPGA experiments, and hardware architecture

The existing circuit development has concrete source evidence:

- [Circuit syntax](../../Applications/Circuits/Syntax.lean) defines typed gates,
  cartesian composition, and an interpretation into a target gate algebra.
- [Digital semantics](../../Applications/Timing/Digital.lean) packages signal,
  Boolean-value, and interval-linear timing interpretations with stability
  preservation, including an exact matrix representation of timing.
- [Circuit correctness](../../Applications/Circuits/Correctness.lean) derives
  `compile_value`, `compile_stable`, and `compile_matrix_stable` for source
  programs from those interpretations.

[ADR 0008](../adr/0008-timing.md#consequences-and-limits) bounds these results:
they do not supply Verilog export, place-and-route, physical measurements,
metastability analysis, or stateful feedback. A correctness theorem about the
stated signal model does not establish those engineering results.

The [hardware extension proposals](../extensions.md#hardware-research-and-external-realizations)
separate additional work by its question and evidence:

| Work | Question and deliverable |
|---|---|
| Hardware architecture research | Recover and compare primary sources, including Tabula and functional-language architectures; identify principles, assumptions, and candidate experiments. |
| Hardware architecture derivation | Derive contrasting realizations under a shared specification, making locality, communication, storage, spatial duplication, and temporal reuse explicit. |
| External hardware integration | Select an external interface and supply representation contracts, conversions, and a stated synthesis/place-and-route trust boundary. |
| FPGA experiments | Test a stated architectural hypothesis with a baseline and measurements. FPGA measurements alone do not establish custom-chip physical efficiency. |

These are proposed scopes in `extensions.md`, which explicitly avoids selecting
a mandatory graph runtime, overlay, or product pipeline. The current circuits
and timing libraries can contribute semantic components to several of them;
their source-directory names do not settle the organization of the broader work.

## Organization implications

[ADR 0001](../adr/0001-modules-and-proof-dependencies.md#decision) assigns
`Applications/<domain>` to implementations with semantic proofs and `Examples`
to compositions between domains. It does not define each `Applications` child
as a standalone software product or require every long-running development to
occupy one such directory. Organization should therefore distinguish work
scopes, reusable library components, checked mathematical applications, and
runnable deliverables. A development may use several existing components and
produce several runnable programs without changing those components' meaning.
