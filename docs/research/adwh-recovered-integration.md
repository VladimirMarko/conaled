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

These results address the selected Chapter 1 developments, selected Chapter 2 material,
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

## Research and remaining ownership

The [continuation handoff](adwh-recovered-handoff.md) reconciles all 46 private
tickets, preserves [useful unimplemented research](adwh-recovered-research.md),
and records the remaining capability audit. The integration review did not
establish exhaustive Chapter 1 or checkpoint-335 capability parity. GitHub #149
owns completion; historical cloud acceptance labels and phase gates are retired.

## Usefulness and observation audit

The #458 audit at `3c064b11` uses useful built mathematics, corrected book
coverage and conaled use as its criteria. The current
[coverage map](adwh-reconstruction-map.md#useful-recovered-mathematics-audit-458-2026-11-11)
assigns every selected Chapter 1/2 source module and generic SearchCounting to
its existing declaration record or concrete #459 residual. It also distinguishes
newly verified official code/errata from inherited printed-page attributions.
The source archive remains evidence, not an authority for copying every wrapper
or preserving a mathematical error.

The following observations were checked against current definitions, statement
signatures, connected examples and existing declaration records. The integrated
fresh acceptance at `3c064b11` validates these unchanged sources; this audit adds
no Lean declaration and does not infer semantic coverage from that build.

| Boundary | Retained contract and useful consumer |
| --- | --- |
| Finite values versus partial observations | Native List replacements retain ordered values, occurrences and explicit Option domains. PartialSpine's ideal/Scott-continuity route retains bottom versus nil, infinite inputs and first-output behavior. PartialSpineFilter composes actual Progress producers; an all-reject infinite input has no finite delivered value. |
| Source order and generic assumptions | Permutation insertion and positional selection retain their own order and duplicate occurrences. Occurrences also serves Kruskal/forest clients. Reachable fold fusion keeps its invariant rather than imposing a global commuting law; scan clients use arbitrary seeds and noncommutative list-valued accumulators. |
| Seed and feedback observations | SeededScan has the actual lagged Mealy realization and productive stream observations; its finite seed-inclusive output has n+1 entries. No unrestricted trace or fixed-point theorem follows. A future #109 compiler consumer can compose existing bridges without rebuilding the scan semantics. |
| Declared work versus erased values | ListExecution/ListFusion/CollapseMaterialization execute their counted recursions; map/fold/concat fusion theorems retain local call prices and structural savings. Collapsing to final values does not supply memoization, delayed payload forcing or Chapter 2 permutation bills. Those stronger contracts remain #459. |
| Numerical validity and exact meaning | NonnegativeArithmetic uses explicit validity and exact logarithm/root meanings; invalid division remains bottom rather than zero. The existing stack/interval pipeline consumes its checked source semantics. Rational sign-qualified growth bridges retain their sign premises, not a blanket identification of one-sided order with norm Big O. |
| Floating witnesses | Floating certificate construction retains actual conversion, sum and division observations. Uniform proper-digit results supply successful finite stages, closed range and length-sensitive error bounds. Decimal-square interval consumers enclose the original exact decimal, even when rounding produces one or underflow produces zero. |
| Recurrence quantifiers | Finite affine folds retain arbitrary initial values and independent weights/tolls, including zero. Eventual hypotheses permit finite exceptions. Two-parameter conclusions use constants/threshold uniform in the other parameter. The zero-toll counterexample is a symbolic negation of Theta, not merely differing finite outputs. |
| Search data | FiniteSearch counts ordered exact-depth occurrences on any state type with finite successors. SearchCount.Valid checks the full frontier list and its depth bound; release can reject an arbitrary producer even when its sum happens to be right. The richer decoder theorem needs no injection. No speedup or queens numeral is claimed. |
| State and accounting | Workload/Potential and BinaryCounter already retain arbitrary seeds, actual intermediate states and both boundary potentials. AddMonoid observations need no commutativity; reweighting a trace to a sum is valid, reconstructing its grouping from that sum is not. This is reused by symmetric lists and counter clients. |

A focused elaborated-type check of
`Examples.ExactGrowth.eventually_value_eq_default` confirms that `WithBot.unbotD`
has payload `NNReal`, followed by `WithBot.some NNReal`. It does not infer a
nested `WithBot Value`. `growth_iff_default_isBigO` keeps both eventual-validity
hypotheses. The checked source of `zero_toll_additive_not_isTheta` chooses a
counterindex beyond an arbitrary proposed threshold and multiplier; it retains
the quantified asymptotic obstruction described in the recovered review notes.

The selected audit found no reason to restore parallel source wrappers for
standard List iteration, signed growth or exact lower-section arithmetic.
Their useful mathematical observations have native owners and checked clients.
The original generic workload/counter modules are already covered by #173;
new demand, dynamic-array, average and permutation-cost contracts are not
established merely by those owners. The coverage map gives each remaining
contract to #459 with observable acceptance cases. It is not an authorization
to remove those contracts or to declare the entire chapter complete.

Validation for this documentation audit consists of source/hash/reference
checks and focused type inspection. `lake build Examples.ExactGrowth` completed
2268 Lake jobs including dependency reuse; this is not a count of freshly built
project modules or a fresh whole-library audit. The subsequent explicit-type
probe exited zero. Existing full acceptance remains at `3c064b11`; independent
review of this audit's conclusions is still required. The exact source licensing
and missing full printed-source evidence remain #149 provenance obligations.
