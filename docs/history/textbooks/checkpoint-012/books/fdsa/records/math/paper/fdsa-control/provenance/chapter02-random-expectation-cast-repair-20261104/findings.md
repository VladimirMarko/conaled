# Priority real-cast correction from a live central attempt

Root reported one actual mean diagnostic from the still-running five-target
attempt3 at b3ccd6617c9a0bd033ab181a77d0e07d4b72100a. The author read the
complete owned diagnostic block: after the earlier toReal rewrites, the
bound retained the real Nat cast `(↑2 : Real)` where the target used the
numeral `2`. RandomQuickSortMean failed; its example job labelled `Ran` is
not a module pass. At this record no terminal aggregate result was supplied.
The adjacent partial-observation.json identifies the observed log snapshot,
not a closed log or final exit. Earlier closed failures remain unchanged.

The pinned `Mathlib/Data/Nat/Cast/Defs.lean` states `Nat.cast_ofNat` with
`[NatCast R] [Nat.AtLeastTwo n]`, exactly normalizing the remaining numeral
cast. The successor separates the rewriting stages: first
`rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h`, then
`simpa only [Nat.cast_ofNat] using h`. Staging the two steps avoids rewriting
the ENNReal Nat cast to an ENNReal numeral before the intended toReal cast
lemma has fired. No extra hypothesis or mathematical inequality is added.

The isolated successor is **1f315fdbb40288d99921164bb3fd8afcbd756e58**,
parent 19879f244a81b03b7ccaabbcf53fc0b355e9985b. It changes only this proof
site in Applications/Resources/RandomQuickSortMean.lean, with two inserted
and one removed line. All 32 public and 15 private source contracts were
compared and remain exactly unchanged; examples and initial random sources
are unchanged. The modified site, its surrounding proof, the exact diff and
the actual observed diagnostic were read back. No claim of elaborated-type
verification is made. Git whitespace checking returned exit 0.

The resource is 16,517 bytes/335 lines, SHA-256
2c7976bf52a2dbed2eb6eb959055acc7ae0df8319c167f0128b63e5c482bd5d3.
The unchanged mean-example SHA-256 is
a00248d8ecb10c425c1376e39ceccd77b6a1c468b952ef838f0494624bc26670.
The author worktree is clean with no .lake. No compiler, cache, other
worktree, ticket or global control was touched. The newly released rank
slice was paused before either new Lean file existed, so this commit contains
no rank work. Its start record remains accurate for the original clean base;
a separate interruption note records this explicitly authorized correction.

This successor is uncompiled. Root exclusively coordinates the next focused
check and will supply the actual closed result for the observed attempt.
The author will append that evidence when supplied, preserving the earlier
partial status. All full-candidate/audit, independent Standards and Spec,
immediate-verification and foundation/chapter acceptance gates remain.
Actual rank and size-recurrence work, harmonic/logarithmic/Big-O results,
separate uniform-input mean and pivot-work qualifications remain mandatory.


## Later terminal evidence for the same observed attempt

Root subsequently supplied the closed result. The author read the complete
15,382-byte closed full log and both result records. Attempt3 at unchanged,
clean b3ccd6617c9a0bd033ab181a77d0e07d4b72100a closed **exit 1** at
2026-11-04T07:12:15.194031+00:00, in 329.7488038879983 recorder seconds
(329.6269083490006 native seconds). Its full-log SHA-256 is
27fffd453a4650aa56976d4cfac2b482fccaae82a8f1ba53bfe38fb5780108ca.
The only owned error is the already corrected real-cast mismatch; the other
failure is root-owned Examples.PermutationOrderBoundary. The downstream
mean example remains unvalidated. `closed-attempt3.json` adds the actual
terminal evidence without changing the partial observation or its original
identity. The source successor1f315fdb remains uncompiled at this update;
no acceptance or verification result is inferred.
