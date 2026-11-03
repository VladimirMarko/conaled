# Adjacent-run compression reconstruction (#157)

`Applications.Sequences.RunCompression` proves that the equality-guarded
suffix fold computes exactly the sequence of adjacent runs. The independent
`Spec` relation compares adjacent original input entries: an equal neighbor
can disappear, and an unequal boundary contributes an output entry. It does
not refer to the fold, `dropWhile`, or an executable compression function.
Separated occurrences remain separate runs.

The implementation uses Mathlib's `List.destutter (· ≠ ·)`, exposed as the
abbreviation `compress`. Inspection of the pinned Mathlib
`Data/List/Destutter.lean` found the needed adjacent transformation, chain
property and injective-map law. Global `List.dedup` has different semantics.
`compress_step` proves the source's adjacent recurrence for this existing
implementation. `compress_spec`, `compress_unique` and `compress_iff` connect
it to the independent relation. `Spec.unique` exposes determinism without
requiring executable equality. The suffix fold is retained as `build`, with
its equality predicate inlined; `build_equality_iff` proves exact agreement
with the same relation.

`List.IsChain (· ≠ ·)` replaces the source's recursive `NoAdjacent` predicate.
Mathlib also supplies `List.dropWhile_idempotent`, which the suffix-fold proof
uses directly. There is no new list representation, generic algebraic class,
or duplicate destuttering algorithm.

## Provenance and remaining declarations

The source snapshot is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md).
Both extracted members were checked against the preserved manifest before
inspection:

| Archive member | SHA-256 |
|---|---|
| `project/adwh-lean/ADWH/Chapter02/Build.lean` | `060fc434c3da0fae5a382af98c96e48ce1828d9c50270c55cd6b3fc9c73e660f` |
| `project/adwh-lean/ADWH/Chapter02/BuildEquality.lean` | `78eaa0d92dbd6d7e8f3cf7ab58b7b19c8ed82fd5be9a4fb9a8971292b5fa48cb` |

The [declaration ledger](adwh-run-compression-provenance.tsv) lists all 49
explicitly named top-level definitions, inductives and theorems in those two
members. Constructor/generated declarations and anonymous source examples are
not separate ledger rows. Each row records snapshot, member, hash, original
name, destination and disposition. Source names are fully qualified.

The equality transformation in `BuildEquality` is reconstructed, including
its first-entry, unequal-neighbor, membership and repeated-prefix properties.
The counted-executor theorem `buildRun_equality_value` remains deferred.
`Build.insert` and `Build.build` are specialized to equality; their generic
predicate interfaces remain outside this slice. The other `Build` declarations
remain reference material: first-failure drop semantics, counted executors,
length and potential bounds, survivors, operation order, and the correction
to the printed charge. Their individual names are retained in the ledger.
Operation counts belong to a separate resource model under #154; this change
makes no runtime or complexity improvement claim. Neither source module nor
the finite-list family is marked wholly reconstructed.

## Checked cases and statement review

The first obligation was to derive `[1,2,1]` from `[1,1,2,1,1]` through an
independent adjacent-input certificate. Mathlib could compute the example,
but lacked the connection to that certificate and the textbook suffix fold.
The new equivalences discharge those missing connections. Subsequent cases
in `Examples.RunCompression` use public results:

| Case | Expected behavior and connection |
|---|---|
| `empty`, `repeated` | Empty stays empty; three adjacent 4s give one 4. Certificates enter through `build_equality_iff` and `compress_iff`. |
| `separated_build`, `separated_compress` | The two 1-runs remain separated by 2. Both consume `separated_spec` through the public equivalences/uniqueness theorem. |
| `signals_build` | Symbols red, red, blue, red give red, blue, red through `signals_spec` and `build_equality_iff`. |
| `relabeled_build`, `relabeled_compress` | The composition `Option.some ∘ Sum.inl` is proved injective. The relation transports through `Spec.map`; the executable result transports through `compress_map`, using Mathlib's `map_destutter_ne`. |
| `noninjective_merges` | A constant map merges all signal runs into one. Mapping the original three-run output retains three units, so unrestricted commutation would be false. |
| `membership_and_chain_insufficient` | `[1,2]` has the same members as `[1,2,1]` and unequal neighbors, yet fails its compression specification. `Spec.unique` proves that failure. |
| `signals_boundary`, `signals_membership`, `repeated_prefix` | Public boundary/membership results and arbitrary positive repeat counts are exercised. |

Statement review covered every new definition and theorem. `Spec` quantifies
over finite lists of an arbitrary type, without an equality procedure or
order. Its constructors compare original neighbors, including after equal
neighbors collapse. Empty and singleton cases ensure that a nonempty constant
run cannot disappear. Uniqueness compares outputs for the same input, not
lists with merely equal membership. `compress_step` preserves every unequal
boundary, and `compress_head` preserves the first entry. The chain and
membership theorems are consequences, never a substitute specification.

`compress` requires `DecidableEq`; its contract works for any such decision
procedure. `build` only requires `BEq` to execute. Its semantic theorems require
`LawfulBEq`, exactly as the source does, and do not require callers to supply
an additional `DecidableEq`. Classical equality in their proofs does not
alter the executable fold. The bridge to `compress` accepts any explicit
decidable equality together with lawful Boolean equality. Relabeling spans
independent source and target universes and requires injectivity, which the
composed-symbol case establishes and the constant-map case shows is relevant.
The positive repeat count is `k + 1`, avoiding a false empty-prefix claim.

The targeted check is `direnv exec . lake build Examples.RunCompression`.
Both modules pass, and `SquareApplications.lean` imports the examples for the
normal full build and exhaustive axiom audit. Full fresh integration checks
and independent Standards/Spec reviews are owned by the coordinating session.
