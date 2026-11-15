# Root assessment — shared logarithm bounds

Recorded 2026-11-03 UTC for FDSA-XL01. This is source/API/mathematical
preparation, not compilation, independent final review or acceptance.

## Complete stopped preparation

All three authors stopped. Root read the complete 427-line source report,
322-line API report, 523-line initial case report and every final case delta.
The final case report has 536 lines. All mathematical expectations are retained.

| Report under research/ | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| logarithm-bounds-source-preflight.md | 30,310 / 427 | `f7891e3ccbe07e56499f36c52d2024246758ff6a127cdf9b576f7445e5e4ae73` |
| logarithm-bounds-api-preflight.md | 32,941 / 322 | `d013d148aea4b7949f7e8c66a7fed3ef32456565073453d1d3cabdf8fa357a5c` |
| logarithm-bounds-case-preflight.md | 32,523 / 536 | `c46b9bba5a4d1d38b1ec03fa2ce55ca41b254be47950c693c577d9d6de9aa270` |

Two report citations were corrected during source readback. The optional
concavity theorem is root-namespace `strictConcaveOn_log_Ioi`; XP01's
accounting declarations are in `Resources`. Root independently checked the
actual namespace contexts at the pinned Mathlib source and exact c28 commit.
The original source report and root's first case snapshot are preserved under
provenance/, with the source correction record in
reviews/logarithm-bounds-source-namespace-finding.json. The case's final delta
also clarifies an additive constant/out-of-domain wording and records the
final source/API identities. No expected value, theorem domain, source scope
or proof route changed. These are report corrections, not compiler failures.

Root also directly read all55 Lemmas_log lines, the actual splay rank/Optimal
locale definitions, the pairing first-pass calculation, the skew logarithm
combination, and the relevant exact Log.Base APIs. The report's complete
eight-theory/archive comparison is credited to its author; root did not repeat
that archive operation. Relevant project policies and C1's full requirements,
addendum and retained final-review handoff were refreshed. No new review loop,
compiler, checker, project hash helper or cache operation was started.

## Bounded decision and original base

A small shared unit is justified by actual independent consumers: C21-074
uses the strict +1 form, and C23-046 uses the sharp +2 form. Select exactly
these two public arithmetic results over ordinary `Real.logb 2`, with positive
Real arguments. Their proofs use existing multiplication, natural-power and
monotonicity laws and the polynomial inequality `4*x*y <= (x+y)^2`. The strict
form is derived from the sharp form; no new analytic or accounting framework
is needed. The bounded search finding is not a claim that no equivalent
theorem exists anywhere in Mathlib.

Choose original source/review base
`07e480f6ec9958d4975bb90151005b84f2907614`, the unchanged repaired C1 candidate.
It remains unaccepted. The new arithmetic module and cases need only pinned
Mathlib plus this existing project context; they do not need XP01, XT01/XT02,
Braun, ordered trees or later algorithm drafts. The canonical `BinaryTree`
carrier, constructors, `numLeaves_pos` and node-count offset already exist in
Mathlib.Data.Tree.Basic. Simple nil/singleton cases can use those directly,
without copying the shared-tree libraries or depending on their unaccepted
examples.

Place the core in Applications/Arithmetic/LogarithmBounds.lean, namespace
Arithmetic.LogarithmBounds. This refines the API report's tentative Resources
path: these are scalar arithmetic laws, not a new resource observation.
Use Examples/LogarithmBounds.lean for connected source substitutions and direct
existing-library clients. A source note, additive reconstruction-map section
and appended public import complete the five-path scope. Exact requirements
are frozen separately before source release.

## Statement and case assessment

The sharp constant2 is attained at every positive equal pair. The strict +1
corollary needs no distinctness premise. Inputs below1 are valid and may have
negative logarithms: the quarter pair gives sharp equality -2=-2 and strict
-3<-2. Zero cannot replace positivity; totalized log values give concrete
false overclaims. A base-independent constant2 is false, and decreasing bases
reverse the monotone order. The public results therefore keep the exact
base-two source domain.

Connected cases use arbitrary canonical binary trees in independent payload
universes, nil over Empty, and singleton children. Natural sizes are cast
explicitly. The pairing substitution is `(n1+n2+1,m+1)` and its sum is
`n1+n2+m+2`; the all-zero case is 2<=2. The printed +1 intermediate transition
would require2<=0. This is the already-retained C23-052 correction, not a new
obligation or a counterexample to the unchanged final Lemma23.2 statement.
The scalar induction-step cancellation can be checked without inventing
pairing heaps or claiming a full pass/cost theorem.

Skew's weak sum and the nonnegative shifted-product estimate use existing
Mathlib primitives directly in bounded examples. They do not need source-name
aliases in the new core. The latter's stronger zero-slack product bound and
the source +1 bound remain visibly distinct. The shifted-minus-one helper
retains its exact >=2 domains in the note; no demonstrated consumer requires
adding it to this common public surface. Its assumptions are sufficient, not
individually minimal. No existing book obligation is deleted by this choice.

Potential offsets and actual tariffs remain distinct. Unweighted splay uses
external-leaf ranks, binary pairing uses nonempty node counts, and list/forest
pairing includes later siblings. Skew's potential is Int-valued. Their
algorithm-specific size identities, potential cancellation, cost casts and
state histories are not consequences of a scalar inequality. The separately
weighted source allows negative potential, so positive weights do not supply
XP01's terminal-nonnegative premise. No XP01 dependency, evaluator or weighted
tree implementation is selected here.

## Preservation and next step

Retain the complete July27 manuscript provenance, dated October26 AFP archive
identity and full1842-byte AFP BSD notice. The supporting archive postdates the
manuscript and is not asserted to be its generating revision. The actual
source-report distinctions between live and commented uses, the two binary
pairing variants, and the unweighted Optimal file remain explicit.

All C19/C21/C22/C23 algorithms, invariants, exact tariffs, multiple-input
history ownership, exercises, static optimality, conjecture statements and
retained source corrections remain mandatory in their chapters. This common
unit does not activate those chapters or accept any inventory row. The exact
initial C2 prefix remains c80eec92f5458eccfd1c34c8314d666c2a1e3847 after repaired
C1 acceptance. Every earlier failed/unknown validation outcome remains.

Capture the clean original base and relevant source/policy identities, freeze
the full requirements, obtain author readiness, and create/expose/upload the
pre-code checkpoint. Only then may root release disjoint source assignments.
C1 attempt3 remains the sole validator. Later prerequisite acceptance,
matching focused/full guarded verification, exhaustive audit, both ordinary
review axes and immediate candidate verification remain required.
