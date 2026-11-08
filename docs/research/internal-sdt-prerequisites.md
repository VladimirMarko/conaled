# Checked assembly prerequisites for internal SDT

[#371](https://github.com/VladimirMarko/conaled/issues/371) now has a constructed
assembly category and program-index lifting infrastructure. This is its first
prerequisite milestone. **The internal SDT provider and its selected-solution
comparison are not complete.** In particular, the new code supplies neither
completeness nor a fixed-point selector. The remaining obligations below belong
to #371 under #289 and are scheduled as #385–#389. #371 remains open until the
selected-solution comparison is complete.

## Model and source boundary

The target remains the effective-topos account in
[the original report](effective-topos-selected-solutions.md),
[the two-certificate report](effective-topos-multiple-certificates.md), and
[the varying-certificate report](varying-selected-certificates.md).
Van Oosten and Simpson's
[*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf),
Definition 3.1 and §3, pp.265–266, give assemblies, partially recursive tracking,
the halting dominance, and a program-index description of lifting. Their
Theorem 1.13 selects a fixed point by extension; Definition 1.15 and Proposition
1.31 distinguish completeness from completeness of a lift. These are source
results, not dependencies admitted into the Lean development.

The implemented category has carriers in `Type u`, realizers in `Nat`, and
hom sets in `Type u`. A realizer relation need not be injective or decidable.
Every carrier element has a realizer, including bottom in the lifted object.
An arrow carries an underlying total function and a proposition asserting
existence of a partial-recursive tracker defined on **every** realizer of each
input. Equality of arrows is equality of underlying functions; code choices
are not observations. The category is constructed, with identity and
composition trackers proved to satisfy that condition.

`programLift A` has carrier `Option A.Carrier`. A realizer of `some x` is a
program which, at input zero, returns a realizer of x. A realizer of `none`
diverges at input zero. The source presentation runs an index on itself;
the checked implementation uses fixed input zero. The computable equivalence
of these presentations and the partial-map classification theorem remain
explicit obligations. We therefore call this a program-index lift, without
claiming a checked dominance classifier. Lean's host `Option` does not make
every case analysis an assembly arrow: a caller still owes a tracker.

## Reused infrastructure and checked claims

The inventory uses the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` from `lake-manifest.json`.
`Mathlib.Computability.Partrec` supplies recursive-function closure;
`Mathlib.Computability.PartrecCode` supplies codes, evaluation, computable
code constructors and `exists_code`. The category instance uses Mathlib's
ordinary `Category` interface. Searches of the local and Mathlib category
sources found no existing realizability assembly category to extend. This is
an inventory finding, not a claim about all Lean libraries.

| Module | Checked result |
|---|---|
| [Assembly](../../SquareKit/Assembly.lean) | Assembly category; code witness for every arrow; encoded objects; computable maps as arrows; natural-number arrows exactly computable functions; products with projections, pairing and uniqueness. |
| [AssemblyLift](../../SquareKit/AssemblyLift.lean) | Program-index lifted objects; actual trackers for lifted maps and the unit; identity, composition and unit naturality. |
| [AssemblyCertificates](../../Examples/AssemblyCertificates.lean) | The existing independently specified bounded certificates as assemblies; tracked proper embeddings; composition and selected-record preservation through two changes; Boolean and erasure controls. |

The certificate specification is reused from
[VaryingPartialCertificates](../../Examples/VaryingPartialCertificates.lean):
all finite values satisfying the bound are valid, and the trace is fixed by
the counter. A chosen seed specifies a result separately. The new maps reuse
`embed` and `embed_selected`, but prove their computational tracking directly.
Their proofs do not invoke the external ordered solver or its continuity
contract. The old external client remains unchanged and included in the audit.

`selected_changes` preserves the full specified record through capacity
expansion and value translation. The checked instance maps value 2 in `Fin 4`
to value 3 in `Fin 7`, retaining `[2,1,0]`. This proves transport of the
specified record, **not** that an internal SDT selector produces it. Both
embeddings remain non-surjective on the entire certificate family.

The controls distinguish three observations. Distinct selected values can
both be defined, so `isSome` is not injective. Boolean negation is a tracked
endomap without a total fixed point, while its lifted map fixes bottom.
Finally, a zero evaluation bound returns no answer for the program returning 3, although
that program realizes a defined lifted natural number. This last calculation
uses Mathlib's bounded code evaluator, whose bound restricts numbers encountered
during evaluation rather than counting execution steps. The existing countdown
finite-fuel control remains unchanged. Neither is a new adequacy theorem for
the countdown client.

## Exact remaining dependency graph

The nodes below name required theorems or constructions, not record fields
to be assumed by a future client. `P0` is the checked milestone above.

| Node | Prerequisites | Required deliverable |
|---|---|---|
| [P1 / #385](https://github.com/VladimirMarko/conaled/issues/385): admissible partial maps | P0 | Construct pullbacks and the needed subobject semantics for assemblies. Define saturated recursively enumerable supports. Prove that program-index lifting with its unit classifies precisely the corresponding partial maps. Give tracked equivalences between zero-input and diagonal-input presentations. |
| [P2 / #386](https://github.com/VladimirMarko/conaled/issues/386): lifting monad | P1 | Construct generic lift multiplication with a tracker and prove the monad laws. Prove lift comparisons for the admitted slice maps using P1's pullback and classifier constructions; this node does not construct the certificate state family or its algebra. |
| [P3 / #387](https://github.com/VladimirMarko/conaled/issues/387): iteration and extension | P2 | Construct I, F, inclusion, successor and infinity with their trackers. Prove the initial strict-algebra and final-coalgebra universal properties. Establish the extension-selected fixed-point theorem for the constructed structures. |
| [P4 / #388](https://github.com/VladimirMarko/conaled/issues/388): complete certificate family | P1, P3 | Supply the required exponentials and prove completeness of N, completeness of its lift under the halting hypotheses, and closure under exponentials and retracts. Build the context-dependent bound filter on `L(N)^N`, prove its tracking/idempotence, identify its fixed subobject with the certificate state family, and prove extension uniqueness over arbitrary admitted contexts. |
| [P5 / #389](https://github.com/VladimirMarko/conaled/issues/389): selected client comparison | P2, P3, P4 | On P4's constructed certificate state family, construct the coordinatewise union algebra with tracked evaluation/reassembly and prove its algebra laws using P2. Then construct the countdown functional as an internal arrow. Derive its selected solution from extension at infinity, prove equality with the independently specified partial graph, and derive both parameter-change laws from local algebra and extension laws. Recover the unique-certificate client and keep disabled bottom, unequal selections with equal domains, and finite-fuel controls. |

The graph is `P0 → P1 → P2 → P3`, with `(P1,P3) → P4` and
`(P2,P3,P4) → P5`. P5 constructs the concrete state algebra only after P4
supplies its object and evaluation/reassembly infrastructure; P2 supplies the
generic monad laws independently of that family. P1 is the next bounded obligation. The current examples
construct each fixed finite fiber and its maps; they do not establish a
dependent product or the uniform slice theorem required at P4. No universe
classifier is present. Any future internal-language interpretation needs its
own soundness and universe-size account. Operational countdown adequacy is
separate from P5 and must name its program semantics.

## Statement review and decision limits

The statement review checked the quantifier over all realizers in `Tracks`,
termination before returning the target realizer, and function equality rather
than tracker equality. `nat_tracked_iff` recovers computability from a tracker's
behavior, so admission does not silently allow arbitrary natural-number maps.
Product uniqueness holds for all admitted arrows. The lift's inhabitation
proof explicitly constructs constant and divergent programs. Its map tracker
generates composed code without deciding termination, including on bottom.

The certificate maps preserve bounds and trace data. Their full-arrow
composition law precedes the selected-record example. The independent
expected result remains 3 with `[2,1,0]`; the negative controls have concrete
inhabitants. The finite-fuel case does not infer divergence from exhaustion.
These checks cover the new definitions, general laws and applications; they
do not establish the missing P1–P5 claims.

Adopt this assembly infrastructure as a prerequisite for the source model.
Defer general SDT selection until P1–P5 are proved. Retain the external
ordered-domain provider on its own contract; no adapter to that provider is
an acceptance condition here. Neither route receives a productivity claim
from these examples. A shared blind spot is the cost of constructing uniform
context-dependent objects: successful fixed-fiber examples do not measure or
discharge it. #107 stays paused, #108 remains unselected, and #260 inactive.
