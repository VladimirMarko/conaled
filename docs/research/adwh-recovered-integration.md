# Recovered ADWH foundations

This integration adapts the mathematical changes from external source commit
`059fccc9b409d7ce01361daef9ca17483a343218`, originally based on
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, to conaled's later development.
The incoming branch's final recurrence slice had not completed its cloud review
workflow. All imported results therefore undergo the local build, exhaustive
axiom audit and independent review together, rather than inheriting that
workflow's acceptance labels.

## Maintained scope

| Development | Shared/application owners | Connected cases and scope notes |
| --- | --- | --- |
| Finite search counting and certificates | `SquareKit.FiniteSearch`, `Checking.SearchCount`, `Search.Counting` | [SearchCounting](../../Examples/SearchCounting.lean), [counting contracts](adwh-search-counting.md) |
| Finite lists, accumulation and permutations | Existing `ListFusion`, `Iteration`, sequence and occurrence owners | [Accumulation](../../Examples/Accumulation.lean), [PermutationSearch](../../Examples/PermutationSearch.lean), [finite correspondences](adwh-finite-correspondence.md) |
| Partial list observations and continuous operations | `PartialSpine`, `IdealCompletion`, existing Progress producers | [PartialSpineLimits](../../Examples/PartialSpineLimits.lean), [PartialSpineFilter](../../Examples/PartialSpineFilter.lean), [directed limits](adwh-directed-limits.md) |
| Numerals and floating models | `Numerals`, `Floating`, existing interval observations | [FloatingNumeralsUniform](../../Examples/FloatingNumeralsUniform.lean), [uniform guarantees](adwh-floating-uniform.md) |
| Measured execution and growth | Existing `Resources.Measured`, `Workload`, `Potential`; list/guarded-build extensions | [GuardedBuild](../../Examples/GuardedBuild.lean), [ResourceGrowth](../../Examples/ResourceGrowth.lean), [list costs](adwh-list-resources.md) |
| Finite sums and discrete estimates | `FiniteSums`, `DiscreteScales`, `HarmonicBounds`, `LogarithmicSums` | [GeometricSumScan](../../Examples/GeometricSumScan.lean), [DiscreteEstimates](../../Examples/DiscreteEstimates.lean) |
| Exact arithmetic and growth | `NonnegativeArithmetic`, `ExactGrowthBounds`, existing relational compilation and interval semantics | [ExactArithmeticPipeline](../../Examples/ExactArithmeticPipeline.lean), [ExactGrowthApplications](../../Examples/ExactGrowthApplications.lean), [contracts](adwh-exact-arithmetic.md) |
| Finite and uniform recurrence bounds | `FiniteRecurrences`, `Resources.Recurrences` | [ResourceRecurrences](../../Examples/ResourceRecurrences.lean), [RecurrenceScans](../../Examples/RecurrenceScans.lean), [contracts](adwh-recurrences.md) |

These results cover the supplied Chapter 1 scope, selected Chapter 2 material,
and generic search counting. They do not complete Chapter 2, the textbook, or
[#149](https://github.com/VladimirMarko/conaled/issues/149). The concrete
queens-16 numeral proof is excluded. Resource theorems price their declared
executors; finite value equality does not establish machine performance,
parallel span, productivity, or floating error bounds without further premises.

## Reuse and integration

The integration retains every public-entrypoint import from the later baseline
and adds the recovered example imports before module documentation. Shared
mathematics stays in `SquareKit`; domain execution and semantic contracts stay
in `Applications`; connected specializations and universal compositions stay
in `Examples`.

Partial-spine limits use Mathlib ideals and Scott continuity, with the existing
Progress observation and producer interfaces. Exact arithmetic uses the existing
first-order syntax, relational compiler theorem, stack and interval backends.
Measured list clients use the established execution and potential interfaces.
The occurrence extraction and append-cost changes replace duplicated local
operations in forest and tree-flattening clients, preserving their contracts.
The Lean, Mathlib, Lake and Nix pins and verification tools remain unchanged.

## Source provenance and validation

[Checkpoint 335 intake](adwh-checkpoint-335-intake.md) records the external
source identity and the delta against the existing checkpoint-233 inventory.
The development-specific TSV ledgers retain source identities, declaration
mappings and scope qualifications. Embedded cloud log identities, reviewer
session state, historical acceptance statuses and repeated capture records have
been removed. These tables describe correspondence, not validation receipts.

The cloud recovery archives, runtime compatibility kit, private tracker, partial
downloads and Git bundle are not part of this repository or its build. Archived
handoffs do not govern local execution. The retained source commit is an
identifier, not imported Git ancestry.

Acceptance uses the repository's ordinary immutable-candidate build and
exhaustive axiom audit, independent Standards and Spec review, and immediate
candidate verification. The proof audit checks every integrated mathematical
declaration; statement review checks the intended claims and their assumptions.
Existing connected cases cover the recovered claims, including noncommutative
scan order, unknown versus completed list ends, invalid arithmetic versus zero,
zero toll/base recurrence boundaries, and uniform versus pointwise growth.
