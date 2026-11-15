# Independent bounded review — #1011 Extract plan

**Outcome: clear for planning; no actionable findings.**
This is an independent source/reuse-plan review, not either ordinary chapter
implementation review axis and not chapter acceptance. It establishes no new
compiled theorem, executable result, performance measurement, or compiler
correctness claim.

## Exact reviewed inputs and scope

- Frozen plan: `../specs/1011-Extract.md`, SHA-256
  `eccc61e739b5a3ccc0e496ad13828a93b76ec925f3bd80047b799c833a9846ff`,
  45,603 bytes, 626 lines. Its identity was checked before and after the
  assessment, with no author correction required.
- Complete VFA 2.1 `Extract.v`: SHA-256
  `c132273a13fafe176573469e664b9cbe8dd3366ec00e2f9a3ab8ab1d42a2e15d`,
  13,003 bytes, 393 lines. I read the complete chapter, including prose,
  assumptions, proofs, admissions, tactics, commands, and optional exercise.
- Complete auxiliary `test_searchtree.ml`: SHA-256
  `109e94b84632608b05e2c00081e98b2050a05dd9c5180241aa70486e7620e279`,
  935 bytes, 24 lines. Its actual loops and timer placement were inspected
  independently of the source prose and the author's account.
- Inventory: `../source/Extract.inventory.json`, SHA-256
  `79583ef29684f9b16e6b4adb86e91f35738186cc7841e17ad9c2a7193a42c755`.
- Inspected project HEAD:
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, with a clean working tree at
  the final read-only check. The accepted ADT predecessor does not yet exist.
  Future SearchTree/ADT/SourceInsertion reuse is an explicit later obligation,
  not an assertion that those chapter implementations are already accepted.

The review followed AGENTS, architectural/domain guidance, GLOSSARY, the
shared language direction, ADRs 0001/0010, the implementation workflow,
README development/build/audit rules, and local user requirements. Related
predecessor plans and the applicable computational/resource/tree-reuse notes
were checked at their consumption boundaries. Root retains ownership of the
running candidate gate, tracking, and durability integration.

## Coverage and source fidelity

The record table contains all **34 inventory IDs exactly once and in inventory
order**, with no additional IDs. The counts match the chapter: 14 definitions,
seven source assumptions, eight source-proved declarations, two tactic
definitions, and three admissions. All **four exercise names and exact source
ranges** match, including the four-star optional `int_elements` at lines
339–345, whose inventory has no named declaration. All **13 extraction-command
line numbers** match in order: 40, 47, 58, 59, 60, 86, 114, 127, 131, 245, 349,
350, and 358. There is no aborted proof.

This comparison is supplemented by the complete source read; it does not
treat lexical inventory coverage as the whole chapter. The plan also retains
the prose obligation to justify `sortZ`, the finite-integer warning, proof
erasure/dependency distinctions, runnable standalone code, the ML workload,
and corrections or qualifications to informal resource claims.

The Nat, Int and word sorting presentations preserve insertion before an
equal head and tail-first sorting. The source sortedness predicate is adjacent
decoded non-strict order; the plan requires its constructor rules and an
explicit transitivity bridge to the repository's pairwise `KeySorted`.
`sort_int_correct` retains input-to-output permutation of the **original
words**, not merely their decoded images. The repository's opposite
`StableSort.perm` orientation is correctly identified. Stable record clients
do not add an order or equality decision on payloads.

The tree adapter retains both strict-comparison tests in their source order,
the newly supplied key/value in the equality replacement branch, arbitrary
payloads and caller defaults. `lookup_insert_eq` and `lookup_insert_neq`
remain statements about every raw tree, without a BST premise. Extract's
`elements_aux` is correctly identified as the fast accumulator traversal,
with the arbitrary-accumulator identity on raw trees required before reuse.

The unnamed optional exercise has substantive coverage: full-subtree BST,
preservation, bounds/default distinction, raw completeness versus BST-guarded
soundness, both absence directions, the default-independent value witness,
strict projected-key order and original-key uniqueness, fast/slow traversal,
replacement enumeration and separator splitting, and both partial-map
observations with their valid-tree coherence. These are proposed
specializations of predecessor contracts. The plan does not infer absence
from lookup equal to a default, map canonicality from one default-valued
observation, or structural equality from observational equality.

## Integer assumptions and executable branches

The seven source assumptions become exactly four data parameters and three
proved law obligations. No surjectivity, decoder inverse, arithmetic law,
global machine-integer axiom, or payload default instance is added. Weaker
requirements are retained where appropriate: permutation needs no ordering
law; sorting and decoding compatibility need no decoder injectivity; same-key
lookup uses irreflexivity; the distinct-original-key table law needs the
identity information supplied by injectivity.

The three realizations have distinct justified roles: unbounded Int covers
the source Z algorithms, signed BitVec supplies a finite mathematical model,
and Int64 supplies the concrete Lean runtime demonstration. The 63-bit model
has range `[-2^62, 2^62)`; the Int64 model has range `[-2^63, 2^63)`. Width-zero
BitVec laws are separated from positive-width range characterization and
conversion statements. The plan requires conversion bounds and both signed
endpoints rather than silently wrapping generated inputs.

The actual pinned declarations support the provider claims:

- `BitVec.slt`/`sle` compare `toInt`; their decide and iff lemmas give the
  stated Boolean reflection. Ordinary BitVec ordering and `ult`/`ule` are
  unsigned. `eq_of_toInt_eq`/`toInt_inj` prove injectivity for every width.
- `BitVec.toInt_ofInt` uses balanced remainder. The self-conversion theorem
  explicitly takes positive width and both range bounds. `toInt_add` is
  modular; `toInt_add_of_not_saddOverflow` carries the stated overflow guard.
  The proposed four-bit `7 + 1` example is a valid mathematical boundary
  case, still awaiting its checked implementation.
- Int64's comparison propositions use signed BitVec comparison; `decLt` and
  `decLe` have actual runtime overrides. The injection, order, range and
  conversion lemmas have the claimed types. Their logical proofs are not
  presented as verification of the native overrides or host compiler.
- `LinearOrder.lift'` really exists and generates decoded-order decisions,
  min/max and comparison. The plan correctly warns that blindly choosing it
  could change the runtime comparison being demonstrated. The existing
  `reflectedLt` example actually uses `decidable_of_bool`, supporting the
  proposed proof-carrying adaptation of the supplied Boolean operation.

The no-overflow replacement does not become an extra law needed by sorting or
trees. Proof terms in Prop and specification functions in Type are correctly
distinguished. Preserving a value equation does not alone establish that
decoding has disappeared from the executable dependency path.

## Workload, timing, and cost boundary

Direct inspection confirms all three consequential corrections to the ML
program. The tree is fully built before the timer starts. Random queries call
`Random.int n` afresh, so duplicate writes and unsuccessful queries are
possible. The hit count is returned by `test` but discarded by `print_test`.
For consecutive inputs, descending j with `f j = n-j` supplies increasing
keys `0,…,n-1` in both phases and makes the unbalanced tree a right chain.
The original three sizes, lack of explicit seed/repetitions, and misleading
insertion-and-lookup label are all accurately recorded.

The plan requires both a labelled source-shaped run and controlled stored or
reproducibly generated input sequences for later comparison. RNG-in-loop and
pre-generated-query observations remain different experiments. Actual count
and independent binding checks are required; the expected random hit count
is never assumed to equal n. Signed-range checks, zero-size handling,
deterministic replay, resource limits, result consumption and honest failed
or skipped large scenarios are explicit.

Pinned `randNat` includes both range endpoints, normalizes reversed bounds,
and threads generator state; `IO.rand` updates a shared generator seeded by
`IO.setRandSeed`. The proposed `[0,n-1]` adaptation for positive n and explicit
state/serialized IO are appropriate. The plan does not claim a uniformity
proof or OCaml PRNG identity. The actual `IO.monoNanosNow` documentation is
monotonic nanoseconds since an unspecified origin; its recorded meaning is
kept separate from the source `Sys.time` observation.

The source's unary comparison wording is corrected through the staged
lockstep model's actual `min n m + 1` theorem and difference-only obstruction.
The draft remains explicitly unaccepted. Native Nat/Int costs, logarithmic
bit costs, constant machine-word cost and expected random-tree height do not
follow from reflection. Tree shape/path counts, semantic erasure and observed
runtime remain separate contracts. Fixed-width increasing families require
representability and distinctness bounds.

## Provider identity, architecture, and limits

All **28 source/work-state/project/dependency hashes** in the plan's final
tables match the actual inspected files. Consequential project types were
read directly: sorting specifications/mapping/uniqueness, BinaryTree's actual
carrier and map, Square composition/vertical alignment and same-universe
restriction, fold-fusion base/preservation/step premises, measured bind and
erasure, the staged unary model, and the existing bounded benchmark harness.

The design reuses ordinary parameters, idiomatic carriers, separate
observations/laws and existing preservation tools. It does not create a new
integer, comparator, tree, ADT or extraction hierarchy. Concrete native and
direct runner evidence is a bounded later execution obligation, with no
mandatory OCaml backend or toolchain change. Historical timing and theorem
names are not presented as implementation evidence.

The default shell could not see the installed native Lean source path. An
approved read-only execution accessed the six exact pinned core files and
verified their hashes and declarations. No compiler, benchmark, proof gate,
cache action, configuration change, source mutation or chapter acceptance
was performed by this review.

## Findings and disposition

| ID | Status | Finding |
| --- | --- | --- |
| — | None | No actionable omission, false provider claim, weakened source statement, unjustified strengthening or unsupported acceptance claim found. |

The frozen plan is clear as preparation for #1011. Every proposed adapter,
instance, theorem, counterexample, measured result and runnable client remains
pending the ADT predecessor gate and the ordinary chapter implementation
workflow. Acceptance still requires the stable isolated integrated build,
exhaustive proof audit, necessary executable regressions, both independent
review axes and final candidate verification. This report closes no chapter
or local ticket.

Only this review file was written. The author's frozen plan and both project
checkouts were left unchanged.
