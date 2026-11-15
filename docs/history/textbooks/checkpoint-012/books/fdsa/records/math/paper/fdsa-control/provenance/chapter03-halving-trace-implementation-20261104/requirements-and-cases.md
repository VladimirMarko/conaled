# Halving-trace requirements and cases before source

Continue the original Chapter3/full-book loop; no separate acceptance loop.
C03-080 remains open until an actual selector policy yields this positive trace
and proves its actual per-step pivot/partition charge premises. Full83 rows stay.
Only new Applications/Resources/HalvingTrace.lean and Examples/HalvingTrace.lean
are owned, on exact clean 3f42358/e04483. All ten existing rounded/F/group/outside
sources and every older record remain immutable. Root alone runs Lean/Lake.

Encode Halves n sizes as positive singleton stopping, or n::tail where tail
starts at positive m, 2*m<=n and Halves m tail. Early stop at n>1 is allowed.
Prove head equality, positivity, nonempty, length<=sum, initial<=sum, sum<=2*n,
2^(length-1)<=n, recursive edges length-1<=Nat.log 2 n<=Nat.clog 2 n. Use
Mathlib's exact pinned logarithm APIs; singleton has one entry and zero edges.
Expose a floor-halving constructor and an adjacent-size consequence for callers.

For fixed Nat A,B, aligned List.Forall₂ (charge<=A*size+B) implies
sumcharges<=A*sumsizes+B*length<=(2*A+2*B)*n. An independently established
aligned size<=charge gives n<=sumcharges. No unproved algorithmic cost or free
pivot construction is asserted. Natural coefficients can be zero; actual
linear lower bounds require their own charged-work premise.

Independently calculated cases before implementation:
- [8,4,2,1] has positive halving steps, sum15, four entries, three edges.
- [7,3,1] uses floors, sum11, two edges, floorlog2(7)=2 and ceillog2(7)=3.
- [1] has sum1, one entry, zero edges; every Halves1 trace must be this singleton.
- [8] is a valid early stop, sum8 and zero edges.
- Zero initial size is impossible; [3,2] fails because4>3.
- Fixed tariff3*size+2 gives [26,14,8,5], sum53, and bound(6+4)*8=80;
  each charge also dominates its size, yielding the separate lower bound8.
These are scalar traces/charges, not an algorithm runtime measurement.

Before source, primary pinned Mathlib Nat.Log signatures, Forall₂ constructors,
List positivity/sum APIs, and actual book LF1520-1550 were inspected. Existing
frozen inventory/plan remain the full statement source. No failing compiler
probe is fabricated; missing connection to the proposed API is the case gap.
Public inventory includes the inductive type and both constructors. Generated
recursors/eliminators remain subject to explicit inspection and full audit.
