# Certified checker assessment

Assessment for [#137](https://github.com/VladimirMarko/conaled/issues/137),
2026-10-25. Local assessment baseline:
`ad8e7a56de5027eed620486fe63f154eecdd3cd3`; host toolchain:
[`leanprover/lean4:v4.35.0`](../../lean-toolchain).
The source assessment and bounded local experiment below have different evidence
boundaries. Neither reproduces the reported queens result.

## Incoming textbook artifact remains unavailable

[#111](https://github.com/VladimirMarko/conaled/issues/111) and
[#137](https://github.com/VladimirMarko/conaled/issues/137) report incoming
*Algorithm Design with Haskell* work on `cqueens 16 = 14772512` and Lean kernel
optimization. Neither issue supplied an archive, repository URL, revision,
declaration path, kernel patch, or reproduction command when inspected.
Filename searches under `/home/vlad/Code` for queens, algorithm, Haskell and
textbook names, and content searches for `cqueens`, `14772512` and the book
title in Markdown and Lean sources found conaled's existing research references,
but no matching formalization. Searches excluded dependency/build trees;
this is an availability finding for those locations, not proof that no artifact
exists elsewhere.

The exact missing input is the textbook source snapshot containing the
`cqueens` definition and equation proof, its commit or archive digest, its Lean
and dependency pins, any modified kernel source and build configuration, and
the commands and machine/resource conditions behind the reported checking
result. Its provenance, mathematical statement, refinement proofs, transitive
axioms and checking performance remain uninspected. Receiving and inspecting
that package is an unfinished #137 requirement. No textbook result has been
imported or reproduced by this assessment.

## Upstream evaluation and proof checking

Lean 4.35's ordinary `decide` constructs an `of_decide_eq_true` proof using
reflexivity after reducing the decision expression. `decide +kernel` sends the
constructed proof through `mkAuxLemma`, whose result is cached. These are
available routes for small closed acceptance proofs; their source does not
establish that the reported queens workload fits practical resource limits.
See the pinned [Decide implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Elab/Tactic/Decide.lean).

`native_decide` calls `nativeEqTrue`. That function compiles and evaluates a
Boolean expression, then adds a fresh axiom asserting its equality to `true`.
This is an explicit trust boundary, not a kernel reduction proof of that
equation. Such an axiom falls outside this repository's whitelist of
`propext`, `Classical.choice` and `Quot.sound`.
Sources: [Native implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/Native.lean)
and [local proof audit](../../ProofAudit.lean).

`Lean.Meta.ReduceEval` converts expressions into metaprogram values through
weak-head reduction and constructor inspection. Its interface returns
`MetaM α`, with instances for values such as natural numbers, lists and
Booleans. It does not return a theorem relating the value to an independent
declarative semantics. It can support a driver or candidate generator; a
certified consumer still needs checked evidence.
Source: [ReduceEval implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Meta/ReduceEval.lean).

## Local reuse and bounded experiment contract

The existing [graph translation validator](../../SquareKit/Internal/GraphTranslationValidator.lean)
already separates executable certificates from `Validated`, with a
`check_sound` theorem. Its contract pins an environment projection, declaration
identity, emitted syntax and a size limit. It supplies a precedent for a small
validator without asserting support for arbitrary Lean imports.

The implemented experiment checks a **finite ordering certificate**, a list of
values claimed to satisfy a relation at every earlier/later pair. Its independent
declarative meaning is Mathlib's `List.Pairwise R`; it does not mention either
checker. The [reference](../../Applications/Checking/OrderCertificate.lean)
compares each head with every later entry. The realization compares neighbors.
The comparator law connects Boolean operations to `R`; transitivity of `R` is
required only for the replacement theorem. No total order, decidability instance
for `R`, or successful certificate is assumed by that theorem.

On an accepted length-n certificate, inspection of these definitions gives
n(n−1)/2 comparator calls for the reference and max(n−1,0) for the realization.
These are source-level comparison counts, not a proved cost semantics or bounds
on Lean allocation, integer comparison, or compiled runtime. Both algorithms
short-circuit, so rejected-input costs depend on the first failed check.
The finite-list scope excludes dependent syntax, environments, conversion,
imports and arbitrary Lean terms. This is one certificate experiment, not a
claim to formalize the textbook algorithm or a growing Lean kernel fragment.

The shared interfaces already separate executable operations from their laws:
[`Squares.Square`](../../Squares.lean) packages implementation, specification
and a commuting equation; [`Relational.RelSquare`](../../SquareKit/Relations.lean)
packages implementation, specification and relation preservation. Both provide
composition. Exact evaluator agreement can instantiate a square; acceptance
soundness can use a relation without assuming that every certificate succeeds.
An ordinary Lean soundness theorem can remain the public proof interface while
a square exposes composition with a consumer. No replacement of ordinary proofs
with categorical syntax is required.

The actual shared contract is `checkerSquare`, with exact runtime/reference
Boolean equality. `checkedLengthSquare` pairs that square with the unchanged
certificate and composes it with `releaseSquare`. `checkedLength_correct`
establishes that the consumer releases its length exactly when the declarative
pairwise judgment holds. Ordinary Lean users can call `reference_correct`,
`adjacent_correct` and `refinement` directly. `accepted_nodup` demonstrates a
further ordinary consumer: an accepted strict natural-number certificate has
no duplicates. These APIs reuse `Squares.exact` from `SquareKit.Combinators` and introduce no
parallel category or law-transport framework. Mathlib supplies the chain/pairwise equivalence under transitivity.

### Checked cases and statement review

The initial worked expectation was that `[2,5,9]` releases `some 3`, whereas
`[2,5,5]` rejects. The missing connection was the public checker/refinement
interface, developed here; no artificial failing theorem was retained.
[Checked uses](../../Examples/OrderCertificate.lean) retain these cases, the
empty and singleton certificates, decreasing entries, and a nonstrict relation.

| Claims | Statement review and retained evidence |
|---|---|
| `reference_correct` | Universally quantifies over finite lists and comparator laws; concludes an iff with all-pairs semantics, without transitivity. |
| `adjacent_correct` | Concludes chain semantics for any relation. It does not claim all-pairs soundness without a law. |
| `refinement`, `checkerSquare` | Require `IsTrans α R`, and conclude Boolean equality for all lists, including rejected lists. The successor relation on `[0,1,2]` provides a checked counterexample to dropping transitivity. |
| `releaseSquare`, `checkedLengthSquare`, `checkedLength_correct` | Preserve the input through shared pairing/composition; release is exactly acceptance, including `some 0` for the empty list. No certificate correctness premise is smuggled into construction. |
| `lt_law`, increasing/empty/singleton | Natural strict order satisfies the comparator law; positive length cases use `checkedLength_correct`, with hypotheses independently discharged by arithmetic decision or `Pairwise.nil`. |
| duplicate/decreasing/nonstrict/nontransitive | A duplicate and a decrease reject under strict order; nonstrict comparison instantiates refinement at a different relation; successor adjacency accepts while reference rejects. These concrete arithmetic expectations are independent of the general proof. |
| `accepted_nodup` | Uses refinement and reference correctness before transporting `<` to `≠`. It assumes successful strict-order checking, not uniqueness itself. The increasing case shows that premise is satisfiable. |

No source predicates were weakened to make cases pass. The implementation uses
ordinary function and relation APIs; author effort is a comparator law and,
for the optimized replacement, a transitivity instance. Extending this to a
new mathematical setting would require its own suitable finite sequence and
relation interpretation; this experiment does not implement arbitrary internal
languages or erase meaningful differences between settings.

### Reproduction and measurement boundary

Run `direnv exec . python3 scripts/benchmark-order-certificate.py`. The script
creates and retains a directory under `.lake/order-certificate-*`, copies the
affected local import closure, and compiles it from source. It supplies
only those fresh outputs and pinned external caches on `LEAN_PATH`. The existing
exhaustive audit implementation runs with its root import changed to this
closure, then also audits each generated benchmark theorem. The production
entrypoint imports the retained examples for the normal full build/audit.

Each Lean process uses two threads, a 60-second CPU and wall limit, and Lean's
4096 MiB memory limit (`-M4096`, not an OS resident-memory guarantee). Proofs use
10,000,000 heartbeats and recursion depth 100,000. Runtime calls use `lean --run`;
the measured inner interval includes constructing lists and checking them,
with 20 different offsets per size. This is executable observation, not a
kernel proof or verification of a compiled binary. The input is `List.range n`
shifted by offsets 0 through 19, so all 20 certificates should be accepted.

Closed proof processes establish the same declarative pairwise statement for
`List.range n`, once via the reference and once via the optimized checker. The
successful Boolean check uses `decide +kernel`; the ordinary theorem then
transports it to pairwise semantics. Wall timings include process startup,
imports, elaboration, kernel checking and exhaustive audit. They are **not** an
isolated measurement of kernel CPU time. An import-only baseline is reported
separately, without subtracting it to claim a pure checking time.

### Observed run

The final local run on 2026-10-25 used Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Linux 6.18.56 x86_64,
and Intel Core i9-14900HX. The checked-in manifest SHA-256 was
`dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`.
The generated inputs, commands, source hashes and logs were retained in
`.lake/order-certificate-5vwzix2o` and copied to the supervision handoff record.

| n | Reference runtime, 20 inputs | Adjacent runtime, 20 inputs | Reference proof process | Adjacent proof process |
|---|---:|---:|---:|---:|
| 64 | 6.318 ms | 0.290 ms | 0.736 s | 0.678 s |
| 256 | 91.283 ms | 1.181 ms | 1.405 s | 0.704 s |
| 1024 | 1434.441 ms | 4.793 ms | not run | not run |

All runtime rows accepted 20 of 20 inputs. The import-only baseline took
0.614 s; the runtime process as a whole took 2.244 s. These are single-run
observations on this machine, with no statistical or asymptotic performance
claim. The proof rows include the audit import and audit execution; the baseline
imports the example module only. Differences cannot be read as isolated kernel
speedups. No attempt was made to run `cqueens 16`.

Fresh compilation and the exhaustive audit passed for all ten local modules in
the affected closure: 460 kernel-safe declarations, including 193 theorem
declarations. Each generated proof was audited as an `Examples` module too,
including its `decide +kernel` auxiliary: 462 declarations and 195 theorems.
The only transitive axioms were `propext`, `Classical.choice`, and `Quot.sound`.
The existing whole-repository source guard and public import-coverage logic
also passed over 510 modules. The final candidate also passed `direnv exec . ./check.sh --jobs 2`: all
510 modules were freshly checked, followed by the full exhaustive axiom audit.
That run took 513.42 seconds, including 6.81 seconds for the audit, and admitted
only the same three foundational axioms. The full log is retained with the
supervision handoff record. Independent Standards/Spec and originator review
remain separate delivery gates; these measurements do not assert review approval.

## Ownership decision and remaining obligations

This experiment supports retaining a small, proof-carrying algorithm adapter
using upstream list theory and shared squares. It supplies no evidence that
owning a growing Lean-fragment checker would outperform upstream adapters.
Owning a small checker is useful when its declarative judgment and refinement
proofs are reusable independently of Lean metaprogramming. The existing upstream
adapters suffice for building expressions and submitting ordinary proof terms
to the host kernel. The bounded experiment can test the former benefit without
committing to arbitrary import compatibility, replacement of Lean's kernel, or
verification of compiled binaries. Those commitments require separate syntax,
environment, conversion and runtime contracts; none follows from soundness of
a finite certificate checker. This scope follows [#137](https://github.com/VladimirMarko/conaled/issues/137)
and the existing [kernel connection assessment](verified-emission-kernel-connections.md).

Keep the incoming artifact inspection open after local implementation: record
its exact equation and assumptions, distinguish reduction proofs from added
axioms and executable output, inspect kernel changes, reproduce stated limits,
and only then identify specific reusable definitions or optimization laws.
