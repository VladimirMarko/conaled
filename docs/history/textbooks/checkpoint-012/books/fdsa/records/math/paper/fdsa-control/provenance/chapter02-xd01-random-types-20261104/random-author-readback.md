# Random quicksort: complete author source and elaborated-type readback

Date: 2026-11-04. Author assessment for the initial direct random-pivot slice.
This is not either independent review axis and is not a complete-candidate
check, axiom audit, immediate candidate verification, or acceptance decision.

## Exact source and checked identity

The held author candidate is
`bb4fb243bb7b16ae8bef921fec479a86f2b01c90` on
`work/fdsa-ch02-random-pivot`. The central checked candidate is
`dfaf68114d1dda4e15628c94c3d988c3f5457c49`.
The author worktree was read as clean. Byte comparison used both immutable
Git blobs and the central working copies, with all three copies identical:

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/RandomQuickSort.lean` | 509 | 23,601 | `c2fcc81b6bd7a4de8b7a9dc476dad62322701609a53b4ea58772f1d9a81307a2` |
| `Examples/RandomQuickSort.lean` | 203 | 8,255 | `4f5a21d1656423ac1307b1ca8fe651cd794d70da576ecd14f65d68cc290c424d` |
| `Applications/Resources/QuickSort.lean` dependency | 474 | 21,782 | `e98024f6b741e1aba1fb1e38b419eee2e1acad76a8a40e669752f54775783263` |

Every line and proof in the 509-line random resource file and 203-line example
file was read. The full 62-declaration elaborated output was read consecutively
from line 1 through line 1,188: 87,257 bytes, SHA-256
`38119532e0476e3fa4870d924bed6484ed26267f1d6eae5707b41f99eb4728ac`.
The exact output is [random-types.txt](random-types.txt), and its declaration
inventory is in [type-output-sections.json](type-output-sections.json).
All 39 public resource declarations and 23 public examples were compared to
their source statements. The seven private resource proofs and private
`pair_exercise` example helper were included in the full source readback.
The other 72 declarations in the joint inspection belong to XD01 and are not
claimed as this author's readback scope.

## Actual closed validation evidence

The complete [focused attempt4 log](../chapter02-xd01-random-focused-20261104-attempt4/full.log),
outer result and native result were read. The qualified official Lean/Lake
4.35.0 launcher used one Lean thread and the exact four requested targets:
`Applications.Resources.DifferenceListCosts`, `Examples.DifferenceListCosts`,
`Applications.Resources.RandomQuickSort`, and `Examples.RandomQuickSort`.
This corrected attempt closed **exit 0**, 9.201865451 seconds, at unchanged
central HEAD `dfaf68114d1dda4e15628c94c3d988c3f5457c49`, with a clean final status.
Its complete log is 4,186 bytes, SHA-256
`514c8e71be97d10be7bb0c181e2dc3605423186b0adbfc085c122f63bee0896a`.
The result states `verification_record_present: false`.

The [134-type inspection terminal result](result.json) and
[native result](native/result.json) also closed **exit 0** at that exact clean
candidate, in 13.325960255 seconds. The complete joint log has 123,793 bytes,
SHA-256 `5027831298792411bde1622e6ad00aef816a0f0f41c97e372139eb8a47afe182`.
The 62-name section above is the complete random-pivot portion. This source
and type pass does not substitute for `check.sh` or its audit/verification.

Prior results remain unchanged:

- `chapter02-extended-sorting-focused-20261104-attempt1` at
  `5d7a479549f5acd64a9e5adb418ab48780c238ef` closed exit 1. The original random
  core failed, and the downstream example's `Ran` entry was not a pass.
- `chapter02-variants-xd01-focused-20261104-attempt1` at
  `4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9` closed exit 1. The corrected
  random core passed individually; its original examples still failed.
- `chapter02-xd01-random-focused-20261104-attempt3` at `dfaf681...` closed
  exit 1 in 28.108006885 seconds. Its complete 4,553-byte log (SHA-256
  `cf73d4026d6f0840340787abeef5d93a525ff25dfb1b0a9641a69ad76a5750d0`) and
  result were read in full. It replayed the passing resource and built the
  corrected examples successfully, but the requested nonexistent target
  `Applications.Sorting.RandomQuickSort` caused aggregate failure. Attempt4
  corrected the requested module path; it did not change these source bytes.

The bounded corrections remain the recorded proof-only successors
`254a4162fa6aeeb7ab2a1ceea5139e5772a5865b` and
`bb4fb243bb7b16ae8bef921fec479a86f2b01c90`. No earlier failed attempt has been
relabelled as passing, and no validation log was overwritten by this report.

## Source and elaborated contract assessment

**Outcome: no concrete mismatch found in this complete author readback.**
The following checks were made against actual elaborated types as well as
source definitions and proof bodies.

1. **Occurrence sampling.** `uniformIndex m` is a normalized PMF on
   `Fin (m+1)` with inverse natural cardinality weights. Every valid index is
   supported, the singleton index law is pure, and `uniformIndex_event` counts
   occurrences. Neither finite payload enumeration nor payload equality is
   hidden in these statements. The repeated `[true,true,false]` event is 2/3.
2. **Actual recursion.** `run` has arbitrary payload universe `Type u`,
   returns `PMF (Measured (List α) (Nat × Nat))`, and requests no payload
   instances. Its nonempty branch samples again, selects by the valid index,
   erases that occurrence, consumes both actual `filterRun` values, binds
   actual recursive results, and consumes `appendPivotRun`'s returned value
   and cost. Termination uses strictly smaller indexed remainders and filters.
   `run_cons` is derived from those operations; it is not a cost-only stand-in.
3. **Values and assumptions.** `run_perm` and `run_length` require only
   actual support. `run_sorted_compatible_on` retains input-local comparator
   compatibility and transitivity of the observed key relation. `runOn`
   initially needs key `LT`/`DecidableLT`; its concrete split and correctness
   use `LinearOrder κ`, with independent payload/key universes. Sortedness is
   not asserted for an arbitrary Boolean comparator. No stability claim is
   accidentally present.
4. **Source tariff.** Empty observation is (1,0), singleton (5,3), local
   exercise toll is `4*rest.length+3`, and local append toll is
   `left.1.length+3`. Values use `left ++ ([pivot] ++ right)`. The exact
   source association is preserved in both definition and unfolding.
   The independent append-association examples expose counts 5 versus 7.
5. **All-path bounds.** Every stated bound retains the actual support
   premise. For input length n, T is at most `2*n^2+2*n+1`, A is at least
   `3*n`, `2*A` is at most `n^2+5*n`, and A is at most T. Thus T <= T+A <= 2*T.
   The stronger literal bound uses the natural floor division explicitly;
   it has not become an unintended real division statement.
6. **Projected laws.** `exerciseLaw` and `literalLaw` have codomain `PMF Nat`
   even when payloads inhabit arbitrary universes. They map the same actual
   run. Their finite supports follow from the actual all-path bounds.
   `exerciseLaw_cons` is a proved map/bind identity of those distributions,
   with the selected remainder and both actual child laws. It has no assumed
   sampler, rank law, distinctness hypothesis, or expectation conclusion.
7. **Duplicate behavior.** The all-false and constant-key theorems retain
   their explicit input-local hypotheses. They derive the actual joint cost
   law (T,A) = `(2*n^2+2*n+1,3*n)` for every size. The replicate execution
   theorem also proves the returned value. Arbitrary equal-key tags need not
   retain their order: the supported reversed two-tag output has mass 1/2 and
   violates the existing `Stable` predicate.
8. **Consequential finite cases.** The actual two-key exercise law is pure
   13, with append masses 1/2 at 6 and 1/2 at 7. The actual three-distinct-key
   exercise law has mass 1/3 at 21 and 2/3 at 25, and zero elsewhere. The
   corrected arithmetic proof did not alter these values. Empty `Empty`
   payloads, arbitrary-universe singletons, all-equal three-element input,
   arbitrary tagged families, and general payload-bound clients all retain
   their advertised assumptions and conclusions.

The source preserves `autoImplicit false` and `warningAsError true`; bounded
compiler corrections did not suppress linters or change mathematical
statements. The current focused/type results are evidence for this initial
slice only. They do not supply a whole-project declaration audit.

## Mandatory continuation and hold

No public expectation or integrability theorem exists in this initial pair.
The next bounded preparation is finite lower expectations, genuine real
integrability, and the actual recursive bind-mean identity, followed by the
same-run append-inclusive mean comparison and connected mean examples.
The expectation plan is not yet a saved or released implementation at this
report's timestamp. Its proposed destination is
`chapter02-random-expectation-preparation-20261104/`.

The distinct-key occurrence/rank bijection, inherited key distinctness,
length-indexed actual mean recurrence, harmonic formula, logarithmic/Big-O
bound, and separate uniform-input first-pivot mean remain mandatory. Pivot
selection, index lookup/removal and random-bit work are outside both current
observations; their separate qualifications remain in force. A PMF denotation
is not a checked random-bit sampler or a physical runtime claim.

Chapter 1 remains accepted at `07e480f6ec9958d4975bb90151005b84f2907614`.
This child has not accepted foundation candidate
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761` or Chapter 2. The full frozen
Chapter 2 scope and 112-obligation clarification remain unchanged. Independent
Standards and Spec reviews, exact immutable-candidate checks, audit, immediate
verification and root-controlled local integration remain required.

No Lean source, Git ref, dependency, cache, build output, ticket or coverage
file was changed for this assessment. After saving this report and its handoff
append, the author holds all source/ref/control writes for checkpoint 0088.
