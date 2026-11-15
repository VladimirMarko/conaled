# Chapter 3 insertion-selection auxiliary slice

Candidate `8fef3ea5964f058f1c0036f53414d5d06fa56e59`, tree
`b7d5cc92f65a3896659cebf7fcf933178018db52`, is the first source slice on
`work/fdsa-ch03-mom-execution`. Its parent is the assigned immutable value/pivot
candidate `9ff4d92e20eeabde29fd91b78c37786019e9613b`. The six inherited files are
unchanged. This is uncompiled development work in the existing complete
Chapter 3 loop, with no chapter acceptance or completed-obligation claim.

## Requested serial check

Build `Applications.Resources.SelectionAuxiliary` and
`Examples.SelectionAuxiliary` in the root-owned qualified checkout. The core
imports the accepted insertion/list-call libraries and the focused-passed
CountRank source. It does not import the still-uncompiled mathematical pivot.
The candidate's inherited pivot remains part of future whole-chapter scope.

Only the two announced new files changed, with 277 source lines:

| File | Public declarations | Private / anonymous declarations |
| --- | ---: | ---: |
| `Applications/Resources/SelectionAuxiliary.lean` | 20: two definitions and eighteen theorems | 0 / 0 |
| `Examples/SelectionAuxiliary.lean` | 20 theorems | 0 / 0 |

`auxiliary-candidate1.json` binds both file hashes, immutable lineage, inherited
file identities, source inventory and the complete forty-name statement input.
`AuxiliaryStatements40-candidate1.lean` uses the supported detailed printer
options, including `pp.deepTerms`, `pp.proofs`, and `pp.maxSteps 1000000`.
No actual printed types exist yet. The finite printer budget still requires
inspection of every actual block for omissions after execution.

## Definitions, intended claims and source correspondence

`slowSelectRun k xs` sequences the existing measured insertion sort with the
existing sequential optional lookup on its actual result. There is no extra
wrapper charge. The value theorem connects that execution to the existing
canonical sorted index through `sortOn_eq_insertionOn`; it never assigns the
insertion cost to the canonical merge-sort specification. The exact total count
is insertion work plus `min k n + 1`. Under the book's valid-rank condition
`k<n`, it becomes insertion work plus `k+1`, giving `n^2+3*n+1`.

Successful results are equivalent to the existing zero-based `RankedAt`
predicate. Failure is exactly `n<=k`, and the public interface bridge goes to
`sortSelect (k+1) xs`, preserving public rank zero as failure. The operation
requires a linear order but no `Nodup` or `Inhabited` assumption. The `Fin 0`
empty-input examples explicitly exercise a payload type with no elements.

`slowMedianRun xs` first executes the existing measured length operation, then
calls slow selection at `(n-1)/2`. Its value is the existing lower median, its
exact work is length work plus the reached slow selection work, and successful
results have the lower occurrence rank and belong to the input. Failure is
exactly empty input. For nonempty input, the source bound is `n^2+4*n+2`; every
positive size at most five therefore has the required coarse bound 47.

The two base-budget lemmas add the source selector's entry charge and cached
length work to a valid slow-selection call. They prove `n^2+4*n+3` and then
483 when `n<=20`. They are arithmetic facts about this explicit composition,
not a claim that a nested selector or its recursive cost has been implemented.

Source scope is C03-027, C03-032, C03-033, the per-chunk consequence needed by
C03-035, and the base arithmetic needed by C03-038. The direct book passages
were read from the pinned extracted text: LF1761–1780, LF1823–1848 and
LF13847–13874, corresponding to printed pp.39–41 and348. Python `splitlines`
also splits the text's form feeds and controls, so its initially displayed
coordinates were not treated as the claimed LF ranges; the corrected LF read
is saved as tool `dc02d3`. Frozen requirements and the complete proof plan were
retained, including the source corrections and remaining eighty-three IDs.

## Connected cases and statement assessment

Expected values and counts were calculated before implementation in
`auxiliary-preparation.json`. Cases consume the new value, exact-cost and bound
theorems rather than depending on proof bodies:

- Empty optional selection costs two; empty median costs three. These are
  explicitly declared extension counts, outside the source valid-rank theorem.
- Selecting zero from `[7]` returns seven with four calls; its median takes six.
  Invalid indices one and seventeen both return `none` with five calls.
- The reversed even pair `[7,2]` returns the lower median two with ten calls.
  `[4,4]` returns four with nine calls, retaining equal central occurrences.
- The ascending and descending length-five ranges both return median two, with
  twenty and thirty calls respectively. A derived theorem exposes that the
  same median value does not imply equal work.
- The repeated-value rank in `[3,1,3,2]` is transported through a constant
  monotone map, demonstrating value semantics when all keys merge without
  claiming resource preservation under that map.
- Universal valid-selection, short-chunk, combined median-value/budget, and
  cutoff clients keep the exact domain assumptions. At the cutoff, entry plus
  length plus last-rank selection costs 83 on the ascending range and 273 on
  its reverse; both fit the retained source bound 483.

All forty written headers and both complete sources were read back in tool
`5c6561`. The source assessment checks rank conventions, occurrence multiplicity,
actual measured operations, nonempty median premises, natural subtraction and
division, uniform constants and the optional failure boundary. No premise assumes
the desired result or its cost. Actual elaborated-type assessment remains
pending, along with independent Standards and Spec review.

## Actual evidence and remaining work

`git diff --cached --check` exited zero. The commit command (tool output
`77111d`) completed with actual exit zero, and the post-commit source was clean.
No Lean/Lake command, compiler
probe, cache action, toolchain change, qualified-checkout modification, root
entrypoint/shared-document change, or accepted-branch change was performed by
this author. Source-only preparation does not establish compilation, audit,
type-inspection or acceptance success. The likely first-check risks are exact
rewrite matching and ordinary arithmetic/linter elaboration, not permission to
weaken the statements or the source tariff.

Next source work after the first actual check is the measured positive-size
chop recursion with separate take/drop calls, then proof-carrying payload
medians and their actual measured map. Mapping `Option` values and discarding
failures would add an uncharged traversal and is not supplied as a substitute.
The member-certified nested selector, its all-input termination and valid-rank
correctness, the exact conditional source-cost recurrence, and the monotone
scalar majorant remain required. The first-child median must be computed by
the recursive selector, with no assumed correct oracle. The sharp affine bound
and the actual read/tariff bridge remain separate later obligations.

For eventual whole-chapter integration, import `Examples.SelectionAuxiliary`
from the shared public root and map these results in the reconstruction record
under root ownership. Those shared files are unchanged. The author is HELD
after this immutable handoff pending actual compilation or a correction request.
