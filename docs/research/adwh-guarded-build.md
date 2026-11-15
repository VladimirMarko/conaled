# Guarded build: values and measured work

The adaptation preserves the generic Haskell right fold and adds its actual
predicate-call and inserted-cons accounting to the existing resource library.
The owner is `Resources.GuardedBuild` in
[`Applications/Resources/GuardedBuild.lean`](../../Applications/Resources/GuardedBuild.lean).
It uses the existing `Resources.Measured`, `pure`, `bind`, `run` and potential
theorems. The pure [run-compression owner](../../Applications/Sequences/RunCompression.lean)
and its independent adjacent-input `Spec` retain their existing interfaces.

## Counted operations and independent value contracts

All generic operations quantify over `α : Type u` and arbitrary Boolean
predicates. They require no equality, order, reflexivity or transitivity law.
`dropRun q xs` charges one unit per actual predicate call. A first failing call
costs one and returns the untouched suffix, including its arbitrary tail. Empty
input costs zero. `insertRun p x xs` executes that drop through `Resources.bind`
and then charges one for the new cons. These units do not price predicate
internals, dispatch, allocation bytes, arithmetic bit complexity or elapsed time.

`DropSpec q xs rest` independently states that `xs = pre ++ rest`, every member
of `pre` passes `q`, and `rest` is empty or begins with a failing entry. It does
not define correctness by equality with the executor. The generic `BuildSpec`
first relates the input tail to an intermediate list, then applies this
first-failure relation before prepending the current entry. Soundness and
uniqueness connect both relations to the actual returned values.

The pure insertion is `x :: xs.dropWhile (p x)`. The pure build is
`xs.foldr (insert p) []`; its measured recurrence builds the suffix first:

```text
buildRun p []       = Resources.pure []
buildRun p (x::xs)  = Resources.bind (buildRun p xs) (insertRun p x)
```

The generic drop, insertion and build length bounds are respectively
`|rest| ≤ |xs|`, `|out| ≤ |xs| + 1` and `|out| ≤ |xs|`.

## Exact potential and the failed-test unit

Write `S rest` for `survivorCharge rest`: zero at nil and one otherwise.
The exact additive identities retain the stopping test:

```text
dropWork + |rest| = |input| + S rest
insertWork + |new| = |old| + 2 + S rest ≤ |old| + 3
```

An individual insertion may scan a long prefix. Inserting into an all-passing
list of length `k` costs `k + 1`; the local potential bound does not assert
constant actual insertion work. Natural-number equalities retain both boundary
potentials without truncated subtraction.

For constant false, inserting `1` into `[2]` returns `([1,2],2)`: one failed
test plus one cons. Thus `work + |new| = 4`, while `|old| + 2 = 3`.
`failed_test_charge_two_counterexample` states this about the actual
insertion executor. For constant true on the same input, the pair is `([1],2)`;
exhaustion adds no failed test at nil. Source 335 describes the former as a
correction to a printed charge-two account. The textbook PDF has not been
inspected, so that attribution belongs to the supplied formalization and this
explicit counting convention.

The whole-build identity and bounds, with `n = xs.length`, are:

```text
work + |result| = 2*n + survivors p xs
work + |result| ≤ 3*n
n ≤ work ≤ 3*n
```

`survivors` sums the actual nonempty-remainder indicators along the executed
trajectory, with `0 ≤ survivors ≤ n`. It is defined using `Resources.budget`;
`survivors_nil` and `survivors_cons` retain the source equations. This is a
mathematical analysis of that trajectory; its evaluation is not an additional
uncharged program operation. The lower work bound records one actual inserted
cons for every input entry.

## Reuse of the existing execution and potential laws

The pair bridge `buildRun_eq_run_reverse` identifies the suffix-first executor
with `Resources.run (insertRun p) xs.reverse []`. Here reversal describes
command order. The recursive executor does not perform a physical reversal.
An implementation that calls the measured list reverse would owe its separate
`Resources.ListExecution.reverse_work` cost of `2*n + 1` in that model.

The proof uses the existing run/bind and append laws, then instantiates
`Resources.run_potential_exact` with list length and charge `2 + S rest`.
The reusable statement keeps arbitrary initial and final list lengths; the
whole-build theorem specializes the initial list to nil. A private arithmetic
lemma separates the constant-two portion of this particular budget.
`Resources.run_constant_charge` gives the charge-three upper bound. These
connections use the existing [potential owner](../../Applications/Resources/Potential.lean),
without a second state interpreter or telescoping framework.

## Equality specialization and connected consumers

Let `RC` mean `Applications.Sequences.RunCompression`. The bridges
separate executable Boolean equality from its semantic laws:

| Interface | Assumptions on `α` | Value conclusion |
| --- | --- | --- |
| Generic `buildRun p` | None | The generic guarded fold |
| `buildRun_equality_value` | `BEq` | Existing `RC.build xs` |
| `buildRun_equality_of_spec` | `BEq`, `LawfulBEq` | Any `out` certified by `RC.Spec xs out` |
| `buildRun_equality_eq_compress` | `BEq`, `LawfulBEq`, `DecidableEq` | Existing `RC.compress xs` |

The source's `BuildEquality.buildRun_equality_value` concludes equality with
`compress`, so its ledger destination is the last bridge. The weaker
same-named erasure bridge alone does not discharge that source statement.
`RC.Spec` itself needs no equality instance and preserves separated runs.
Membership and unequal neighbors are consequences, not a replacement for it;
the existing `membership_and_chain_insufficient` client remains relevant.
Value equality never supplies an equality of measured costs.

`Examples.GuardedBuild.buildHead` uses the actual measured
`Resources.ListExecution.head` after the completed equality builder via
`Resources.bind`. Its value is the original `head?`, its work is the builder's
work plus one, and its bound is `3*n + 1`. Empty input returns `none` with work
one. The value theorem requires lawful Boolean equality; construction and work
bounds require only `BEq`. Nonempty input still pays for the whole finite build
before observation.

In `Examples.ListPipelines`, `measured_compressed_forest` connects a certificate
over the distributed output to the actual
`((TreeFlattening.fromTs trees).filter p).map f` producer through
`forest_distribution`. The concrete intermediate `[2,2,3,2]` compresses to
`[2,3,2]`; the exact stage pair is `([2,3,2],8)`, with bound twelve. The certificate value
bridge uses `LawfulBEq`; the stage work bound requires only `BEq`.
This budget prices compression's predicate tests and inserted cons cells;
tree traversal, filter, map and certificate checking lie outside this stage.
The existing unmeasured `forest_result` contract is retained. The extension
stays in the owner of the private forest definitions.

## Source identities, cases and retained history

The source is successor 335, archive SHA-256
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Its `sources.tar.xz` contains these members beneath `project/adwh-lean/`:

| Member | SHA-256 |
| --- | --- |
| `ADWH/Chapter02/Build.lean` | `060fc434c3da0fae5a382af98c96e48ce1828d9c50270c55cd6b3fc9c73e660f` |
| `ADWH/Chapter02/BuildEquality.lean` | `78eaa0d92dbd6d7e8f3cf7ab58b7b19c8ed82fd5be9a4fb9a8971292b5fa48cb` |

The [56-entry ledger](adwh-guarded-build-provenance.tsv) preserves all exact
source IDs, line coordinates, signatures and file hashes: 49 named entries
and seven examples. It retains 17 existing equality destinations, dispositions
and scopes exactly, and maps the remaining 32 named adaptations. Source
examples `Build@229` and `BuildEquality@158` remain distinct rows while sharing
the eight-element certificate client. The other five coordinates retain the
false/true insertion pairs, false whole-build pair, separated-run compression
and existing empty compression contract with its measured empty companion.

The earlier [run-compression ledger](adwh-run-compression-provenance.tsv) remains
unchanged. Its rows 11 and 18 specialize `Build.insert` and `Build.build` to
equality inside `RC.build`. The generic definitions extend those partial dispositions without erasing the
earlier scope or replacing its equality API. Every named row retains all eight fields of the historical ledger, including
its original snapshot, destination, disposition and scope, together with its
row route. Original planning fields are retained separately from current source
dispositions. The historical file's
SHA-256 is `1d1dd75172226f2a939ad1d02c28cdf2d32af400c3867437c54a252643b05382`.

The supplied Haskell `part0/chap2.hs` physical lines 29–30 contain the generic
`build` signature and its `foldr insert []` definition. Their exact fragment
SHA-256 is `8a54f98486d323eb8a298867ea80b1fa5d26b225428f173af9b308a864c7c4d2`.
The following are retained ledger coordinates, not a new inspection of the
textbook PDF or original literate pages:

| Ledger obligation | Retained coordinates | Scope of this slice |
| --- | --- | --- |
| `2.4-build` | Printed 35 / PDF 52 | Generic guarded fold and its value contracts |
| `2.4-build-potential` | Printed 37 / PDF 54 | Explicit local and whole-build accounting |
| `ch02:part0_chap2.hs:L549` | Extracted 29–30; recorded original `chap2.lhs` 549–550 | The inspected Haskell fragment above |
| `ch02-builder-terminal-test` | Chapter 2 correction record | The actual failed-test counterexample |
| `2.2-cost-model` | Printed 27–28 / PDF 44–45 | Only the operations and observation units used here |

These five context obligations are separate from the 56 authored rows. The
shared cost-model item is not closed for the whole chapter. This bounded
development does not establish full Chapter 2 or whole-book completeness.
