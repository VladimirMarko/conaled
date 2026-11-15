# Random quicksort expectation: first compiler findings and proof-only successor

## Boundary and identity

This is the author correction record for the first closed focused compile of
the actual-mean pair. It records a failed check and an uncompiled successor;
it is not a focused pass, an independent review, or an acceptance record.

The author parent is `7b1851cee7fe580a4fe235740b0c07e4ddd8fc58`. The successor
is **`19879f244a81b03b7ccaabbcf53fc0b355e9985b`**, on
`work/fdsa-ch02-random-pivot`. The sole changed source is
`Applications/Resources/RandomQuickSortMean.lean`, with five replaced proof
lines and no change in line count. Both mean definitions, every theorem
statement and hypothesis, imports, options, universes, and all examples are
unchanged. The author worktree is clean and has no `.lake` directory.

The exact first central candidate was
`fff993ec1d041c0a86e7e79a94d13f5be6b92a94`. Its two mean source blobs were
compared with the author parent's blobs and are identical. The central result
closed at 2026-11-04T06:59:27.673295+00:00 with **exit 1**, recorder elapsed
101.64727630000016 seconds; the nested native result records exit 1 and
101.54561406799985 seconds. Initial and final central HEAD agree, with empty
statuses. The complete 17,412-byte/112-line log has SHA-256
`48063b4acf544e1cd977f2ffc039a37024bd01e30bfd42357041d4704de22d84`.

The full log, start, result and native result were read. The source module
failed, so the downstream `Examples.RandomQuickSortMean` job labelled `Ran`
is **not** a proof-module pass. The aggregate also contains independent
PermutationOrder findings, outside this author's scope; those sources were
not changed here. The successful uniqueness pair does not change the failed
aggregate status. There is no matching successful candidate verification.

## Every owned diagnostic and its bounded correction

| Failed location | Actual diagnostic | Correction and pinned justification |
| --- | --- | --- |
| Resource line 64 | Unknown identifier `mul_le_mul_left'` | Use `mul_le_mul_right`, whose current pinned type is `(bc : b ≤ c) (a : α) : a * b ≤ a * c`. This is exactly the left multiplication needed for a nonzero PMF weight. The support split and pointwise bound are unchanged. |
| Resource line 243 | Unknown identifier `i` in the finite lower-sum finiteness assertion | Parenthesize the complete summand `(L i + R i)`, retaining the intended bound variable scope. No summand or finiteness premise changes. |
| Resource line 253 | Unknown identifier `i` in the `change` expression | Add the same summand parentheses on the lower-integral side of the proof-local equality. |
| Resource line 257 | Unknown identifier `i` in the real finite sum of the `change` expression | Parenthesize both actual child means as one summand. The public statement already uses a `let` body containing the two child means and is unchanged. |
| Resource line 307 | Simplification leaves `(↑2).toReal` rather than real `2` | Replace `ENNReal.toReal_ofNat` by `ENNReal.toReal_natCast`. The finite upper bound uses `ENNReal.natCast_ne_top 2`, so the multiplier in the elaborated term is a Nat cast. The same-run inequalities and all finiteness arguments are unchanged. |

The current Mathlib sources were inspected at exact pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

- `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean` gives the actual
  `mul_le_mul_right` type and its neighboring right-factor lemma.
- `Mathlib/Basic/ENNReal/Basic.lean` gives distinct `toReal_natCast` and
  `toReal_ofNat` statements. The former covers the observed Nat-cast term.

No compiler or dependency substitution is proposed. No linter, warning,
proof restriction, validation requirement, or candidate gate was disabled.

## Source and statement readback

All five changed sites and their surrounding proofs were read back against
the actual diagnostic blocks. The complete 32-public/15-private source-level
contract inventory was compared to the previous source: all statement
prefixes agree exactly, with the complete diff independently confirming
that only the five stated proof lines changed. This comparison is a source
check, not an elaborated-type check. The previous full 334+118-line author
readback and per-claim assessment remain applicable to the unchanged source
and are preserved in the earlier draft provenance.

The corrected resource is 334 lines and 16,488 bytes, SHA-256
`135af328490993bc48ff9c8a0ccfd847768fca22329292bd2ee0ff4db21662c0`.
The unchanged mean examples are 118 lines and 5,733 bytes, SHA-256
`a00248d8ecb10c425c1376e39ceccd77b6a1c468b952ef838f0494624bc26670`.
The complete 2,724-byte source diff has SHA-256
`e6da49e0857f7aa4c6f5512e5a41c8a42dcb5a35ae534ca4809c15c738952908`.
`git diff --check` returned exit 0 with an empty closed log.

Actual execution, occurrence sampling, measured returned filters and children,
right-associated append assembly, Nat law projections and support bounds are
untouched. The real mean definitions still integrate those actual Nat laws.
Their genuine integrability still comes from finite lower expectations,
and finite child/sum premises precede the real bind-mean transport.
The literal comparison still transports both observations from the same
actual run. The fixed means 1, 5, 13, 71/3, 8 and 39/2 and the constant-key
quadratic mean examples are unchanged.

## Next boundary

This successor has not been compiled. Root exclusively coordinates the next
focused check and any subsequent exact type inspection. No build, cache,
other worktree, global control, ticket, or coverage write was made by this
author. The initial random pair's earlier focused/type passes remain valid
for their exact unchanged bytes; they do not certify this successor.

The distinct-key occurrence/rank bridge, inherited child key distinctness,
actual size-only recurrence, harmonic identity, logarithmic and Big-O bounds,
the separate uniform-input mean, and pivot implementation overhead
qualifications all remain mandatory. The rank preparation is coordinated
with the harmonic owner through the actual canonical-input `sizeMean`
proposal. It introduces no Lean source or acceptance claim.

Full immutable-candidate validation/audit, both independent review axes and
immediate candidate verification remain necessary. This correction supplies
no foundation or chapter acceptance. The author holds source/ref writes for
root's central validation and returns to HOLD after closing the authorized
report and rank-preparation artifacts.
