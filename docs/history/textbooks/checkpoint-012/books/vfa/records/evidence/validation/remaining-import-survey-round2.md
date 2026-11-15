# Remaining Mathlib.Tactic imports: round-two proposal

Proposal only; no Lean compiler, checkout edit, configuration/cache change, or
primary-process signal was performed. Only this new note is written.
Snapshot: 2026-11-02T10:11:39.041486+00:00. Main and isolated candidate both:
`39c3e2fd0c3a7b39e56373d453a1a17382bc3749`. There were 427 complete project artifact sets.

## Exact proposed replacements and isolated effects

For each listed module, replace its single literal `import Mathlib.Tactic\n`
with the listed `import …` lines **in the displayed order**, each ending in LF.
“Delete the line” means remove that line including its LF. Every other byte,
including all remaining imports, comments, statements and proof bodies, stays
unchanged. This specifies the exact complete proposed bytes; hashes are below.

“Closure” counts the root plus recursively resolved project/package source
imports, including public/meta imports, excluding compiler-distribution
Init/Lean/Std/Lake modules. “Built” counts reverse-closure modules with all
`.olean`, `.ilean`, `.c`, and `.trace` present; these are invalidations,
not newly accepted proofs. “Unbuilt losing umbrella” counts unfinished modules
that lose their sole Mathlib.Tactic path under that row alone. Each individual
row leaves both aggregates with other umbrella paths.

| Module | Exact replacement lines | Closure before → after | Built | Unbuilt losing umbrella |
| --- | --- | ---: | ---: | ---: |
| `Applications.Durability.DiagnosticGraph` | `import Mathlib.Tactic.Linarith`; `import Mathlib.Tactic.Ring` | 3135 → 964 | 2 | 5 |
| `Applications.Interaction.Obligation` | `import Mathlib.Tactic.Tauto` | 3125 → 469 | 0 | 3 |
| `Applications.Linear.Structured` | Delete the line | 3132 → 1438 | 0 | 2 |
| `Applications.Linear.StructuredCosts` | `import Lean.Elab.Tactic.Omega` | 3126 → 720 | 0 | 1 |
| `Applications.Orbifold.ProjectiveMotion` | `import Mathlib.Tactic.Linarith`; `import Mathlib.Tactic.FieldSimp` | 3168 → 2401 | 6 | 22 |
| `Applications.Probability.CoinPaths` | `import Mathlib.Tactic.NormNum`; `import Lean.Elab.Tactic.Omega` | 3670 → 3108 | 0 | 2 |
| `Applications.Probability.FiniteMH` | `import Mathlib.Algebra.BigOperators.Fin`; `import Mathlib.Tactic.Linarith`; `import Mathlib.Tactic.FinCases` | 3122 → 1013 | 0 | 5 |
| `Applications.Sequences.BoundedSummary` | `import Lean.Elab.Tactic.Omega`; `import Mathlib.Tactic.Ring` | 3135 → 783 | 6 | 0 |
| `Examples.ProbabilityCorrelation` | `import Mathlib.Tactic.NormNum`; `import Mathlib.Tactic.FunProp` | 3286 → 3286 | 0 | 0 |
| `SquareKit.Temporal.Monitor` | `import Mathlib.Data.Nat.Basic`; `import Lean.Elab.Tactic.Omega` | 3122 → 155 | 0 | 3 |

The source graph resolved all non-core imports. It includes 954 integrated
project modules: 953 in SquareApplications and the separate managed ProofAudit.
Package sources are the pinned candidate dependencies, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; the toolchain is Lean 4.35.0.
All ten complete root bodies were read. Reverse-client headers, specialist
tactic uses and the concrete provider paths below were inspected; this is not
a replacement for elaborating every client.

## Concrete provider findings and remaining uncertainty

- **DiagnosticGraph:** its own body needs no specialist tactic, but
  DiagnosticStorage uses `ring` at lines 55/75/237/351 and `nlinarith` at 366;
  Examples.DiagnosticStorage also uses both. Keeping Linarith and Ring at the
  existing root preserves those clients without editing their bodies.
  Linarith.Frontend publicly imports Ring.Basic, which supplies `ring1`;
  the actual `ring` macro is in Ring.RingNF at line 208. Hence Linarith alone
  is insufficient for this inspected client requirement. Common tactics remain
  through Finset.Powerset → Multiset.Powerset → List.Zip → List.Basic → Tactic.Common.
- **Obligation:** `tauto` is used at lines 58/66, with its explicit provider
  Tactic.Tauto. Its two example clients use ordinary proof steps and the
  unchanged relational APIs. Their complete bodies were read.
- **Structured / StructuredCosts:** the former uses ordinary proof steps;
  the latter uses `omega` at line 81, also needed in StructuredMeasured.
  Examples.StructuredLinear retains FinCases through Matrix.ToLin →
  RingTheory.Ideal.Span → LinearAlgebra.Span.Basic → Order.CompactlyGenerated.Basic
  → Order.SupIndep → Tactic.FinCases. NormNum.Basic remains through Matrix.ToLin
  → Algebra.Algebra.Subalgebra.Tower → RingTheory.Ideal.Defs → Tactic.Abel.
  **Residual:** the full NormNum umbrella is absent; its three concrete
  integer-matrix equality examples must confirm that retained arithmetic
  extensions suffice. StructuredCosts' implicit list-sum and function-monoid
  simp/instance requirements likewise await ordinary elaboration.
- **FiniteMH:** Linarith publicly imports the full NormNum family; FinCases
  supplies its finite case splits. A concrete named-theorem gap in the initial
  two-tactic proposal was corrected here: `Fintype.sum_bool` is generated in
  Data.Fintype.BigOperators around line 43, and `Fin.sum_univ_succ` in
  Algebra.BigOperators.Fin around line 76. Neither provider remained initially.
  Adding Algebra.BigOperators.Fin covers both; its header publicly imports
  Data.Fintype.BigOperators. The final closure is **1013**, superseding the
  preliminary 970 count. Kernel clients retain their explicit measure imports.
- **Monitor:** Mathlib.Data.Nat.Basic imports the generic order declarations and
  supplies `Nat.instLinearOrder` at line 34; Order.Defs.PartialOrder supplies
  `lt_of_le_of_ne` at 201. Pinned Init publicly imports Init.Data.List, whose
  public imports include OfFn, Lemmas, TakeDrop and Nat. In that core source,
  OfFn lines 44/65 supply length/getElem? facts, Lemmas 573/576 supply any/all,
  and Nat.TakeDrop 39/68/112/151 supplies length/getElem?/nested/append take
  facts. Thus separate Mathlib OfFn/TakeDrop imports are not justified by the
  named requirements inspected. Omega is explicit. The complete FRP.Monitor
  and Examples.TemporalMonitor bodies introduce no additional specialist tactic.
  **Residual:** this particularly small header must still elaborate all
  implicit simplification facts and the two unchanged clients.
- **BoundedSummary:** its own arithmetic uses Omega; resource clients use
  `ring` at Resources.BoundedSummary lines 29/41 and Resources.ByteBuffer
  133/138. Retain Ring rather than dropping it accidentally.
- **CoinPaths / ProbabilityCorrelation:** NormNum and Omega cover CoinPaths'
  numeric/arithmetic proofs; `filter_upwards` is declared in
  Mathlib.Order.Filter.Defs at 544, retained through SpecificLimits.Basic's
  filter imports. Correlation explicitly keeps NormNum and FunProp.
- **ProjectiveMotion:** reuse the exact earlier Linarith/FieldSimp proposal and
  its unchanged source hash in remaining-import-proposals.md. Its source uses
  `nlinarith`, `field_simp`, and the core `exact_mod_cast` macro.
  Remaining client providers were checked, including positivity through
  TransportSegments → Trigonometric.Basic → QuadraticDiscriminant →
  LinearCombination → Positivity.Core; module through CheckedMotion →
  RationalMotion → NumericalBounds → Calculus.MeanValue → Deriv.Slope →
  AffineSpace.Slope → Tactic.Module; and linear_combination through
  MotionUniqueness → ContDiff.RCLike → MeanValue → RCLike.Basic →
  Tactic.LinearCombination.

These are small conservative source-based proposals, not compiler-certified
minimal imports. Retained provider paths establish source dependencies; they
do not establish that all simp registrations, tactic extensions, instances,
generated declarations, or public/private visibility behave identically.
The normal full candidate build must decide those remaining questions.
No body alteration, new assumption, tactic shortcut, or acceptance waiver is
part of this proposal. Local Mathlib paths above are relative to
`vfa-validation/.lake/packages/mathlib/`; core paths are relative to the pinned
toolchain's `src/lean/`.

## Priorities, overlaps and affected clients

Zero-invalidation branches with the greatest unfinished coverage are FiniteMH
(five, or six jointly with Correlation) and the two Structured roots together
(five). Monitor and Obligation each cover three. DiagnosticGraph covers five
unfinished modules at the cost of two completed invalidations. ProjectiveMotion
covers the largest single branch: 22 unfinished modules and six completed
invalidations. BoundedSummary has no unfinished non-aggregate client at this
snapshot, but retaining its umbrella would prevent the aggregate-wide removal.

- **Diagnostics:** completed Graph and Projection; unfinished DiagnosticStorage,
  DiagnosticRelational, Examples.DiagnosticProjection, Examples.DiagnosticStorage,
  and Examples.RetainedHistory.
- **Obligation:** unfinished root, Examples.InteractionInterfaces and
  Examples.InteractionTransport.
- **Structured pair:** unfinished Structured, StructuredCosts, StructuredMeasured,
  Examples.StructuredLinear and Examples.StructuredLinearCosts. The shared
  Measured/Costs example path retains an umbrella if only one root changes.
- **FiniteMH + Correlation:** unfinished FiniteMH, FiniteKernel,
  Applications.Probability.MetropolisHastings, Examples.MetropolisHastings,
  Examples.PreservationBounds and Examples.ProbabilityCorrelation.
  Correlation alone saves no imports; jointly its closure falls 3286 → 2059.
- **Monitor:** unfinished SquareKit.Temporal.Monitor, Applications.FRP.Monitor,
  Examples.TemporalMonitor. **CoinPaths:** unfinished root and
  Examples.ProbabilisticProgress.
- **BoundedSummary:** six completed invalidations: Applications.Sequences
  BoundedSummary/ByteBuffer, Applications.Resources BoundedSummary/ByteBuffer,
  and Examples.BoundedSummary/ByteBuffer.
- **ProjectiveMotion:** completed ProjectiveMotion, StandardForm, Disk, Pose,
  ConnectionAssessment and Applications.Linear.Similitude. Unfinished Orbifold
  clients: CheckedMotion, CommandComparison, DiskConnection, DiskCurvature,
  DiskTransport, MatrixDisk, MotionUniqueness, NumericalBounds, NumericalExecution,
  NumericalSymmetry, PoseConnection, QuarterTurn, RationalMotion, TimedCommands,
  TimedMotion, TransportComparison, TransportFrames and TransportSegments;
  plus Examples.DiskRealizations, NumericalMotion, PathTransport and TimedMotion.

## Joint counterfactual: all ten headers

All **62** affected project modules lose Mathlib.Tactic altogether:
**14 completed** artifact sets would invalidate; **48 unfinished** modules
would lose the umbrella, comprising **46 non-aggregates plus both aggregates**.
The other project modules have no umbrella path to remove. These totals are a
union, not the sum of overlapping row counts.

| Aggregate | Total resolved closure | Project modules | External package modules | Mathlib modules |
| --- | ---: | ---: | ---: | ---: |
| SquareApplications | 5132 → 4760 | 953 → 953 | 4179 → 3807 | 3893 → 3525 |
| ProofAudit | 5133 → 4761 | 954 → 954 | 4179 → 3807 | 3893 → 3525 |

The joint external reduction is 372 modules; the much larger isolated branch
reductions are not additive because many required dependencies are shared.
The full aggregate still imports substantial mathematics required by unrelated
applications. The static check found no remaining Mathlib.Tactic path and no
missing provider among the known specialist tactic names inspected, after
the concrete fixes described above. This does not discharge the stated
implicit-dependency uncertainties.

Root/environment have separately observed severe paging and I/O in the current
guarded build; this survey did not sample processes or establish causation.
**No timing or memory improvement is established by these topology counts.**
Any integration and candidate restart remain root-owned. The ordinary guarded
build, proof audit, regression, independent reviews and final candidate
verification remain required; no VFA chapter is accepted here.

## Exact source identities

The following proposed SHA256 values were computed in memory from the literal
single-line replacements above; no proposed Lean file was written.

| Module | Current source SHA256 | Proposed source SHA256 |
| --- | --- | --- |
| `Applications.Durability.DiagnosticGraph` | `8f49558a9ac21fd23d55c1ad5478d57d785a901715ada62ec5cf90b2e130529a` | `b5a138e524c9d438489bee476bd8bd4cea839df95dcaed281a62cf559408300b` |
| `Applications.Interaction.Obligation` | `053fdb310e95f7383983de03ac3739021e7f87d87e76a59d27c5625fbd863191` | `4a88511cea3f84dcf2d81f5477d7bb94c580c57bf47c94fa33808b2f83ec9340` |
| `Applications.Linear.Structured` | `4354be9787d2d1593de121f911dc4cd97f0539cb89518128581bb86d7f3bec2f` | `5c9bc9083279044c8b0ee68587624556067fefb3d065cafe802a1df5ee2a893b` |
| `Applications.Linear.StructuredCosts` | `6c00cc1e1a73a27c595d9c504948c0b0567f268bcbe698e7c6e236dcab7fc28a` | `328e462f214b45754ab7197d869742ffd3c398c82512867931d3ffa6aebef911` |
| `Applications.Orbifold.ProjectiveMotion` | `76fd6a04ad9c3b283888f7c44b99237339f5f516acb9dedefe98cbe0db44c0c5` | `d0e0920d166555216764e3a20d6c8f3c26ea15415b1072da527654894d491ae3` |
| `Applications.Probability.CoinPaths` | `f8880ba5d62c62cd64f406b4e61be30e824b7d7f140935dd4b8f10fe6bf44850` | `735ce9377cb1d275cc7a1bb4ffd4d6aaff6a5523ac62d7f5dcebc69c91249e84` |
| `Applications.Probability.FiniteMH` | `8b86470a97e577e2e83ece9f40e6d7cfb4afcee11765c915caf257c8e4c5f416` | `5f6d8470d79da75a05655a10543f999b7558bf97abbfa235bd351050a145bad9` |
| `Applications.Sequences.BoundedSummary` | `96133f27b8c3603429bbbb039b7b617df3d1b3f59c1b1c89e44595eade56a847` | `5cf743692c43758c45e62bf55e705da02a83eec728470ec1252589e62e5b1bf3` |
| `Examples.ProbabilityCorrelation` | `45038cca487f212ef69919567257da3af230f4ef8a991362b82ff8f83170e017` | `cedc0840e4c8fbab84f230d0ac083a066337d8a17e0b97740abf4f1a987160a4` |
| `SquareKit.Temporal.Monitor` | `8f9138dccb411976303f1e1b69ceb7a9b61aafebbb00c5b4cec172b9b7139fdd` | `f1b1b28c6ec52c2e948d42ea1b01169bbe77df4911ed9f7082a36406a8a38a23` |

